"""
Beritasaku - Alat pemantau berita berdasarkan titik koordinat.

Alur: koordinat -> nama wilayah (Nominatim) -> berita Google News RSS pada rentang
waktu yang dipilih, dibatasi pada wilayah dalam radius tertentu dari titik.

Dijalankan dengan: streamlit run app.py
"""

import math
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timedelta, timezone
from urllib.parse import quote_plus

import feedparser
import folium
import pandas as pd
import requests
import streamlit as st
from geopy.exc import GeocoderServiceError, GeocoderTimedOut, GeocoderUnavailable
from geopy.geocoders import Nominatim
from streamlit_folium import st_folium

# ---------------------------------------------------------------------------
# Konfigurasi
# ---------------------------------------------------------------------------
st.set_page_config(page_title="Beritasaku", layout="wide", initial_sidebar_state="auto")

MENU_ITEMS = ["Koordinat", "Monitor", "Hasil"]
WIB = timezone(timedelta(hours=7))

DEFAULT_HARI = 30  # rentang waktu bawaan: 30 hari terakhir
DEFAULT_RADIUS_KM = 5
MIN_TANGGAL = date(1900, 1, 1)  # praktis tanpa batas minimum tanggal
HARI_PER_JENDELA = 30  # 1 permintaan RSS maks ~100 artikel, jadi rentang dipecah per ~30 hari
MAKS_JENDELA = 24  # batas jumlah periode per pencarian agar rentang panjang tetap wajar
MAKS_TAMPIL = 300
TINGGI_PETA = 450
TINGGI_DAFTAR = 520
HTTP_HEADERS = {"User-Agent": "Mozilla/5.0 (Beritasaku Streamlit App)"}

ESRI_TILES = (
    "https://server.arcgisonline.com/ArcGIS/rest/services/"
    "World_Imagery/MapServer/tile/{z}/{y}/{x}"
)
ESRI_ATTR = (
    "Tiles &copy; Esri &mdash; Source: Esri, Maxar, Earthstar Geographics, "
    "and the GIS User Community"
)

KRIMINAL_RE = re.compile(
    r"\b(kriminal\w*|pencuri\w*|pencurian|curanmor|pembunuh\w*|dibunuh|perampok\w*|"
    r"perampasan|rampok\w*|begal\w*|penipu\w*|penipuan|narkoba|narkotika|sabu|"
    r"penganiaya\w*|pemerkosa\w*|pencabulan|asusila|pengeroyok\w*|dikeroyok|"
    r"pembacok\w*|dibacok|jambret\w*|penjambret\w*|tawuran|korupsi|tersangka|"
    r"ditangkap|diringkus|dibekuk|residivis|mayat|penculik\w*)\b",
    re.IGNORECASE,
)
LAKA_RE = re.compile(
    r"\b(kecelakaan|laka|lakalantas|laka\s+lantas|tabrak\w*|tabrakan|menabrak|"
    r"tertabrak|ditabrak|karambol|terguling|tewas\s+di\s+jalan)\b",
    re.IGNORECASE,
)

# CSS: tampilan rapi di PC dan layar sempit (Android).
# - Navigasi atas (radio) hanya tampil di layar sempit; di PC memakai sidebar.
# - Tombol sidebar selalu selebar sidebar, judul berita tidak meluber.
CSS = """
<style>
section[data-testid="stSidebar"] .stButton > button { width: 100%; }
div[data-testid="stMarkdownContainer"] { overflow-wrap: anywhere; }
@media (min-width: 769px) {
  .st-key-nav_mobile { display: none; }
}
@media (max-width: 768px) {
  .block-container { padding: 1rem 0.75rem 3rem !important; }
  h1 { font-size: 1.6rem !important; }
  h2 { font-size: 1.35rem !important; }
}
</style>
"""


# ---------------------------------------------------------------------------
# Utilitas umum
# ---------------------------------------------------------------------------
def hari_ini_wib():
    return datetime.now(WIB).date()


def esc_md(teks):
    """Menghindari karakter markdown/LaTeX dalam judul berita agar tampil apa adanya."""
    return re.sub(r"([\\`*_{}\[\]()#+!|~$<>])", r"\\\1", teks or "")


def deteksi_topik(judul):
    topik = set()
    if KRIMINAL_RE.search(judul or ""):
        topik.add("Kriminal")
    if LAKA_RE.search(judul or ""):
        topik.add("Laka Lantas")
    return topik


def bersihkan_nama_wilayah(nama):
    """Menghapus awalan administratif agar cocok dengan cara media menulisnya."""
    return re.sub(
        r"^(kabupaten|kota|kecamatan|kelurahan|desa)\s+", "", (nama or "").strip(), flags=re.I
    )


def parse_koordinat(teks):
    """Mengembalikan (lat, lon). Melempar ValueError bila format salah."""
    teks = (teks or "").strip()
    if not teks:
        raise ValueError("Koordinat belum diisi.")

    bagian = [p for p in teks.split(",") if p.strip()]
    if len(bagian) != 2:
        bagian = [p for p in re.split(r"[\s;]+", teks) if p]
    if len(bagian) != 2:
        raise ValueError("Format tidak dikenali. Isi dengan latitude dan longitude.")

    try:
        lat = float(bagian[0].strip())
        lon = float(bagian[1].strip())
    except ValueError:
        raise ValueError("Latitude dan longitude harus berupa angka desimal.")

    if not -90 <= lat <= 90:
        raise ValueError("Latitude harus berada di antara -90 dan 90.")
    if not -180 <= lon <= 180:
        raise ValueError("Longitude harus berada di antara -180 dan 180.")
    return lat, lon


# ---------------------------------------------------------------------------
# State & navigasi
# ---------------------------------------------------------------------------
def init_state():
    defaults = {
        "menu": MENU_ITEMS[0],
        "nav_radio": MENU_ITEMS[0],
        "koordinat_teks": "",
        "lat": None,
        "lon": None,
        "tgl_awal": hari_ini_wib() - timedelta(days=DEFAULT_HARI),
        "tgl_akhir": hari_ini_wib(),
        "radius_km": DEFAULT_RADIUS_KM,
        "wilayah": None,  # dict: desa, kecamatan, kota, provinsi, negara, alamat, sekitar
        "artikel": [],  # list of dict
        "rentang_berita": None,  # (tgl_awal, tgl_akhir) berita yang sudah diambil
    }
    for key, value in defaults.items():
        if key not in st.session_state:
            st.session_state[key] = value


def set_menu(nama):
    st.session_state["menu"] = nama
    st.session_state["nav_radio"] = nama


def sinkron_dari_radio():
    st.session_state["menu"] = st.session_state["nav_radio"]


def render_navigasi():
    with st.sidebar:
        st.title("Beritasaku")
        for nama in MENU_ITEMS:
            st.button(
                nama,
                key=f"menu_{nama}",
                type="primary" if st.session_state["menu"] == nama else "secondary",
                on_click=set_menu,
                args=(nama,),
            )
    # Navigasi cadangan untuk layar sempit (sidebar tertutup secara bawaan di HP)
    with st.container(key="nav_mobile"):
        st.radio(
            "Menu",
            MENU_ITEMS,
            horizontal=True,
            key="nav_radio",
            on_change=sinkron_dari_radio,
            label_visibility="collapsed",
        )


# ---------------------------------------------------------------------------
# Geocoding
# ---------------------------------------------------------------------------
@st.cache_data(ttl=86400, show_spinner=False)
def reverse_geocode(lat, lon):
    """
    Mengembalikan dict wilayah, atau None bila koordinat berada di area kosong
    (laut lepas, gurun, dsb). Melempar exception geopy bila layanan gagal
    (kegagalan tidak disimpan di cache).
    """
    geolocator = Nominatim(user_agent="beritasaku-streamlit-app", timeout=10)
    lokasi = None
    error_terakhir = None

    for percobaan in range(3):
        try:
            lokasi = geolocator.reverse(
                (lat, lon), language="id", addressdetails=True, zoom=14
            )
            error_terakhir = None
            break
        except (GeocoderTimedOut, GeocoderUnavailable) as e:
            error_terakhir = e
            time.sleep(1.5 * (percobaan + 1))

    if error_terakhir is not None:
        raise error_terakhir
    if lokasi is None:
        return None

    addr = lokasi.raw.get("address", {}) or {}

    def ambil(*kunci):
        for k in kunci:
            if addr.get(k):
                return addr[k]
        return ""

    wilayah = {
        "desa": ambil("village", "suburb", "neighbourhood", "hamlet", "quarter"),
        "kecamatan": ambil("city_district", "municipality", "suburb", "district", "subdistrict"),
        "kota": ambil("city", "town", "regency", "county", "municipality"),
        "provinsi": ambil("state", "region", "province"),
        "negara": ambil("country"),
        "alamat": lokasi.address,
    }
    if not (wilayah["kota"] or wilayah["provinsi"] or wilayah["negara"]):
        return None
    return wilayah


def cari_nama_sekitar(lat, lon, radius_m):
    """
    Mencari nama desa/kelurahan dan kecamatan di sekitar titik (dalam radius) dengan
    mengambil sampel 4 titik (utara, selatan, timur, barat) lalu reverse geocoding.
    Titik yang gagal dilewati begitu saja.
    """
    geolocator = Nominatim(user_agent="beritasaku-streamlit-app", timeout=10)
    jarak = radius_m * 0.7
    dlat = jarak / 111320
    dlon = jarak / (111320 * max(math.cos(math.radians(lat)), 0.01))
    titik = [
        (min(lat + dlat, 90), lon),
        (max(lat - dlat, -90), lon),
        (lat, min(lon + dlon, 180)),
        (lat, max(lon - dlon, -180)),
    ]

    nama = []
    for p in titik:
        time.sleep(1.1)  # patuhi batas 1 permintaan/detik milik Nominatim
        try:
            lokasi = geolocator.reverse(p, language="id", addressdetails=True, zoom=14)
        except Exception:
            continue
        if not lokasi:
            continue
        addr = lokasi.raw.get("address", {}) or {}
        for kunci in (
            ("village", "suburb", "neighbourhood", "hamlet", "quarter"),
            ("city_district", "municipality"),
        ):
            for k in kunci:
                if addr.get(k):
                    nama.append(addr[k])
                    break
    return nama


def buat_query_lokal(terms, kota):
    """Query lokal: nama desa/kecamatan sekitar titik, dipersempit dengan nama kota."""
    bagian = " OR ".join(f'"{t}"' for t in terms)
    if terms and kota:
        return f'({bagian}) "{kota}"'
    if terms:
        return f"({bagian})"
    return f'"{kota}"' if kota else ""


# ---------------------------------------------------------------------------
# Pengambilan berita (Google News RSS)
# ---------------------------------------------------------------------------
def buat_jendela_waktu(tgl_awal, tgl_akhir):
    """Membagi rentang tanggal menjadi periode ~30 hari: list of (mulai, akhir_eksklusif)."""
    total_hari = (tgl_akhir - tgl_awal).days + 1
    n = min(MAKS_JENDELA, max(1, math.ceil(total_hari / HARI_PER_JENDELA)))
    batas = [tgl_awal + timedelta(days=round(i * total_hari / n)) for i in range(n + 1)]
    batas[-1] = tgl_akhir + timedelta(days=1)
    return list(zip(batas[:-1], batas[1:]))


def ambil_feed(query, mulai, akhir):
    """Mengunduh satu RSS Google News untuk satu periode. Waktu terbit dalam WIB."""
    q = f"{query} after:{mulai:%Y-%m-%d} before:{akhir:%Y-%m-%d}"
    url = f"https://news.google.com/rss/search?q={quote_plus(q)}&hl=id&gl=ID&ceid=ID:id"
    resp = requests.get(url, headers=HTTP_HEADERS, timeout=15)
    resp.raise_for_status()
    feed = feedparser.parse(resp.content)

    hasil = []
    for entry in feed.entries:
        waktu = entry.get("published_parsed")
        if not waktu:
            continue
        terbit = (
            datetime(*waktu[:6], tzinfo=timezone.utc).astimezone(WIB).replace(tzinfo=None)
        )

        judul = (entry.get("title") or "").strip()
        sumber = ""
        src = entry.get("source")
        if src and hasattr(src, "get"):
            sumber = src.get("title", "") or ""
        if sumber and judul.endswith(f" - {sumber}"):
            judul = judul[: -len(f" - {sumber}")]
        elif not sumber and " - " in judul:
            judul, sumber = judul.rsplit(" - ", 1)

        hasil.append(
            {
                "judul": judul,
                "link": entry.get("link", ""),
                "sumber": sumber or "Tidak diketahui",
                "terbit": terbit,
            }
        )
    return hasil


def tarik_berita(
    query_lokal, query_global, query_kriminal, query_laka, tgl_awal, tgl_akhir, progress_cb=None
):
    """
    Menarik berita pada rentang tgl_awal s.d. tgl_akhir.
    Mengembalikan (daftar_artikel, jumlah_gagal, jumlah_permintaan).
    """
    jendela = buat_jendela_waktu(tgl_awal, tgl_akhir)
    # Setiap tugas: (kategori, topik_petunjuk, query, mulai, akhir)
    tugas = []
    if query_lokal:
        tugas += [("Lokal", None, query_lokal, m, a) for m, a in jendela]
    if query_kriminal:
        tugas += [("Lokal", "Kriminal", query_kriminal, m, a) for m, a in jendela]
    if query_laka:
        tugas += [("Lokal", "Laka Lantas", query_laka, m, a) for m, a in jendela]
    if query_global:
        tugas += [("Global", None, query_global, m, a) for m, a in jendela]

    artikel_by_key = {}
    gagal, selesai = 0, 0

    with ThreadPoolExecutor(max_workers=6) as pool:
        futures = {
            pool.submit(ambil_feed, q, m, a): (kategori, topik_hint)
            for kategori, topik_hint, q, m, a in tugas
        }
        for future in as_completed(futures):
            kategori, topik_hint = futures[future]
            selesai += 1
            try:
                for item in future.result():
                    if not (tgl_awal <= item["terbit"].date() <= tgl_akhir):
                        continue
                    kunci = item["link"] or item["judul"]
                    if kunci not in artikel_by_key:
                        item["kategori"] = kategori
                        item["topik"] = set()
                        artikel_by_key[kunci] = item
                    if topik_hint:
                        artikel_by_key[kunci]["topik"].add(topik_hint)
            except Exception:
                gagal += 1
            if progress_cb:
                progress_cb(selesai, len(tugas))

    artikel = []
    for item in artikel_by_key.values():
        item["topik"] = sorted(item["topik"] | deteksi_topik(item["judul"]))
        artikel.append(item)
    return artikel, gagal, len(tugas)


# ---------------------------------------------------------------------------
# Halaman: Koordinat
# ---------------------------------------------------------------------------
def halaman_koordinat():
    st.header("Koordinat")

    with st.form("form_koordinat", border=False):
        teks = st.text_input(
            "Koordinat",
            value=st.session_state["koordinat_teks"],
            placeholder="Masukan koordinat lokasi...",
            label_visibility="collapsed",
        )
        rentang = st.date_input(
            "Rentang waktu berita",
            value=(st.session_state["tgl_awal"], st.session_state["tgl_akhir"]),
            min_value=MIN_TANGGAL,
            max_value=hari_ini_wib(),
            format="DD/MM/YYYY",
            help=(
                "Pilih tanggal awal dan tanggal akhir, kapan pun itu. Rentang yang sangat "
                f"panjang dipecah menjadi maksimal {MAKS_JENDELA} periode, sehingga cakupan "
                "tiap periode lebih renggang."
            ),
        )
        radius_km = st.slider(
            "Jarak sekitar titik (km)",
            min_value=1,
            max_value=25,
            value=st.session_state["radius_km"],
            help=(
                "Berita dicari berdasarkan nama desa/kelurahan dan kecamatan dalam jarak ini "
                "dari titik koordinat. Makin kecil, makin spesifik, tetapi jumlah berita "
                "bisa lebih sedikit."
            ),
        )
        submit = st.form_submit_button("Submit")

    if not submit:
        return

    # 1. Validasi
    try:
        lat, lon = parse_koordinat(teks)
    except ValueError as e:
        st.error(str(e))
        return

    if not (isinstance(rentang, (tuple, list)) and len(rentang) == 2):
        st.error("Pilih tanggal awal dan tanggal akhir pada rentang waktu berita.")
        return
    tgl_awal, tgl_akhir = rentang

    st.session_state.update(
        koordinat_teks=teks.strip(),
        lat=lat,
        lon=lon,
        tgl_awal=tgl_awal,
        tgl_akhir=tgl_akhir,
        radius_km=radius_km,
        wilayah=None,
        artikel=[],
        rentang_berita=None,
    )

    # 2. Reverse geocoding
    with st.spinner("Mencari nama wilayah dari koordinat..."):
        try:
            wilayah = reverse_geocode(lat, lon)
        except (GeocoderTimedOut, GeocoderUnavailable):
            st.error(
                "Layanan geocoding (Nominatim) tidak merespons atau koneksi lambat. "
                "Coba lagi beberapa saat."
            )
            return
        except GeocoderServiceError as e:
            st.error(f"Layanan geocoding menolak permintaan: {e}")
            return
        except Exception as e:
            st.error(f"Terjadi kesalahan saat reverse geocoding: {e}")
            return

    if wilayah is None:
        st.warning(
            "Koordinat berada di area kosong (misalnya laut lepas atau wilayah tanpa data "
            "administratif), sehingga nama wilayah dan berita tidak dapat dicari. "
            "Peta tetap dapat dilihat di menu Monitor."
        )
        return

    # 3. Nama desa/kecamatan dalam radius
    with st.spinner(f"Mencari wilayah dalam radius {radius_km} km dari titik..."):
        try:
            nama_sekitar = cari_nama_sekitar(lat, lon, radius_km * 1000)
        except Exception:
            nama_sekitar = []

    terms = []
    for nama in [wilayah["desa"], wilayah["kecamatan"]] + nama_sekitar:
        nama = bersihkan_nama_wilayah(nama)
        if nama and nama not in terms:
            terms.append(nama)
    terms = terms[:10]
    wilayah["sekitar"] = terms
    st.session_state["wilayah"] = wilayah

    # 4. Susun query & tarik berita
    kota = bersihkan_nama_wilayah(wilayah["kota"] or wilayah["provinsi"])
    negara = wilayah["negara"]

    query_lokal = buat_query_lokal(terms, kota)
    query_global = (
        f'"{negara}" (internasional OR global OR dunia OR PBB OR luar negeri)' if negara else ""
    )
    query_kriminal = (
        f"{query_lokal} (kriminal OR pencurian OR pembunuhan OR perampokan OR begal "
        "OR penipuan OR narkoba OR penganiayaan OR ditangkap OR diringkus)"
        if query_lokal
        else ""
    )
    query_laka = (
        f'{query_lokal} (kecelakaan OR "laka lantas" OR tabrakan OR tabrak OR "tabrak lari")'
        if query_lokal
        else ""
    )

    bar = st.progress(0, text=f"Mengambil berita {tgl_awal:%d/%m/%Y} s.d. {tgl_akhir:%d/%m/%Y}...")

    def update(selesai, total):
        bar.progress(selesai / total, text=f"Mengambil berita... ({selesai}/{total})")

    try:
        artikel, gagal, total = tarik_berita(
            query_lokal, query_global, query_kriminal, query_laka, tgl_awal, tgl_akhir, update
        )
    except Exception as e:
        bar.empty()
        st.error(f"Gagal mengambil berita: {e}")
        return
    bar.empty()

    if total and gagal == total:
        st.error("Semua permintaan berita gagal. Periksa koneksi internet lalu coba lagi.")
        return

    st.session_state["artikel"] = artikel
    st.session_state["rentang_berita"] = (tgl_awal, tgl_akhir)

    # 5. Notifikasi
    st.success(
        "Data lokasi dan berita siap dilihat di menu Monitor dan Hasil. "
        f"({len(artikel)} artikel ditemukan.)"
    )
    if gagal:
        st.warning(
            f"{gagal} dari {total} permintaan berita gagal (koneksi lambat atau dibatasi). "
            "Hasil mungkin belum lengkap; Anda dapat menekan Submit lagi."
        )
    if not artikel:
        st.info("Tidak ada berita yang ditemukan untuk wilayah dan rentang waktu ini.")


# ---------------------------------------------------------------------------
# Halaman: Monitor
# ---------------------------------------------------------------------------
def tampilkan_peta(peta):
    try:
        st_folium(peta, height=TINGGI_PETA, use_container_width=True, returned_objects=[])
    except TypeError:  # versi streamlit-folium tanpa use_container_width
        st_folium(peta, height=TINGGI_PETA, returned_objects=[])


def halaman_monitor():
    st.header("Monitor")
    lat, lon = st.session_state["lat"], st.session_state["lon"]
    wilayah = st.session_state["wilayah"]
    radius_km = st.session_state["radius_km"]

    if lat is None or lon is None:
        st.info("Belum ada koordinat. Buka menu **Koordinat**, isi koordinat, lalu tekan **Submit**.")
        return

    if radius_km <= 2:
        zoom = 14
    elif radius_km <= 4:
        zoom = 13
    elif radius_km <= 8:
        zoom = 12
    elif radius_km <= 16:
        zoom = 11
    else:
        zoom = 10

    try:
        peta = folium.Map(location=[lat, lon], zoom_start=zoom, tiles=None, control_scale=True)
        folium.TileLayer(
            tiles=ESRI_TILES,
            attr=ESRI_ATTR,
            name="Esri World Imagery",
            overlay=False,
            control=False,
        ).add_to(peta)
        folium.Marker(
            [lat, lon],
            popup=folium.Popup(wilayah["alamat"] if wilayah else f"{lat}, {lon}", max_width=300),
            tooltip=f"{lat}, {lon}",
            icon=folium.Icon(color="red", icon="map-marker", prefix="fa"),
        ).add_to(peta)
        folium.Circle(
            [lat, lon],
            radius=radius_km * 1000,
            color="#ffcc00",
            weight=3,
            fill=True,
            fill_opacity=0.15,
            tooltip=f"Radius {radius_km} km",
        ).add_to(peta)
        tampilkan_peta(peta)
    except Exception as e:
        st.error(f"Peta gagal dimuat (kemungkinan koneksi internet lambat): {e}")

    st.subheader("Detail Wilayah")
    st.write(f"Koordinat: `{lat}, {lon}`")

    if wilayah is None:
        st.info("Detail wilayah belum tersedia. Tekan **Submit** di menu **Koordinat**.")
        return

    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Kecamatan", wilayah["kecamatan"] or "-")
    c2.metric("Kota/Kabupaten", wilayah["kota"] or "-")
    c3.metric("Provinsi", wilayah["provinsi"] or "-")
    c4.metric("Negara", wilayah["negara"] or "-")
    st.caption(f"Alamat lengkap: {esc_md(wilayah['alamat'])}")
    if wilayah.get("sekitar"):
        st.caption(
            f"Wilayah yang dipakai untuk mencari berita (radius {radius_km} km): "
            + esc_md(", ".join(wilayah["sekitar"]))
        )


# ---------------------------------------------------------------------------
# Halaman: Hasil
# ---------------------------------------------------------------------------
def halaman_hasil():
    st.header("Hasil")
    artikel = st.session_state["artikel"]

    if not artikel:
        st.info("Belum ada berita. Buka menu **Koordinat**, isi koordinat, lalu tekan **Submit**.")
        return

    batas_awal, batas_akhir = st.session_state["rentang_berita"] or (
        st.session_state["tgl_awal"],
        st.session_state["tgl_akhir"],
    )

    wilayah = st.session_state["wilayah"]
    if wilayah:
        st.caption(
            f"Berita {batas_awal:%d/%m/%Y} s.d. {batas_akhir:%d/%m/%Y} untuk "
            f"{esc_md(wilayah['kota'] or wilayah['provinsi'])}, {esc_md(wilayah['negara'])}"
        )

    # Filter
    topik = st.radio(
        "Topik", ["Semua topik", "Kriminal", "Laka Lantas"], horizontal=True
    )
    kol1, kol2 = st.columns([3, 2])
    with kol1:
        kategori = st.radio(
            "Filter", ["Semua", "Berita Lokal", "Berita Global"], horizontal=True
        )
    with kol2:
        urutan = st.selectbox("Urutan waktu", ["Terbaru lebih dulu", "Terlama lebih dulu"])

    df = pd.DataFrame(artikel)

    if topik != "Semua topik":
        df = df[df["topik"].apply(lambda daftar: topik in daftar)]
    if kategori == "Berita Lokal":
        df = df[df["kategori"] == "Lokal"]
    elif kategori == "Berita Global":
        df = df[df["kategori"] == "Global"]
    df = df.sort_values("terbit", ascending=(urutan == "Terlama lebih dulu"))

    st.write(f"Menampilkan **{min(len(df), MAKS_TAMPIL)}** dari **{len(df)}** artikel.")

    with st.container(height=TINGGI_DAFTAR, border=True):
        if df.empty:
            st.info("Tidak ada artikel untuk filter ini.")
        for _, row in df.head(MAKS_TAMPIL).iterrows():
            judul = esc_md(row["judul"])
            link = (row["link"] or "").replace(" ", "%20").replace("(", "%28").replace(")", "%29")
            st.markdown(f"**[{judul}]({link})**" if link else f"**{judul}**")
            bagian = [
                row["kategori"],
                f"{row['terbit']:%d/%m/%Y %H:%M} WIB",
                esc_md(row["sumber"]),
            ]
            if row["topik"]:
                bagian.append(", ".join(row["topik"]))
            st.caption(" · ".join(bagian))
            st.divider()
        if len(df) > MAKS_TAMPIL:
            st.caption(
                f"Hanya {MAKS_TAMPIL} artikel pertama yang ditampilkan. "
                "Gunakan filter untuk mempersempit hasil."
            )


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    init_state()
    st.markdown(CSS, unsafe_allow_html=True)
    render_navigasi()

    menu = st.session_state["menu"]
    if menu == "Koordinat":
        halaman_koordinat()
    elif menu == "Monitor":
        halaman_monitor()
    else:
        halaman_hasil()


main()
import requests
from bs4 import BeautifulSoup
import os
from urllib.parse import urljoin, urlparse, parse_qs

base_url = "https://safari.ethz.ch/ddca/spring2025/doku.php?id=schedule"

response = requests.get(base_url)
response.raise_for_status()
soup = BeautifulSoup(response.text, "html.parser")

pdf_links = []
for link in soup.find_all("a", href=True):
    href = link["href"]
    if ".pdf" in href:  # query içinde olabilir
        full_url = urljoin(base_url, href)
        pdf_links.append(full_url)

print(f"{len(pdf_links)} adet PDF bulundu.")
os.makedirs("pdfs", exist_ok=True)

for url in pdf_links:
    # PDF ismini temizle
    parsed = urlparse(url)
    qs = parse_qs(parsed.query)
    if "media" in qs:
        filename = qs["media"][0]
    else:
        filename = os.path.basename(parsed.path)
    safe_filename = filename.replace("/", "_").replace("?", "_").replace("&", "_")
    filepath = os.path.join("pdfs", safe_filename)

    print(f"İndiriliyor: {safe_filename}")
    with requests.get(url, stream=True) as r:
        r.raise_for_status()
        with open(filepath, "wb") as f:
            for chunk in r.iter_content(chunk_size=8192):
                f.write(chunk)

print("Tüm PDF'ler başarıyla indirildi!")

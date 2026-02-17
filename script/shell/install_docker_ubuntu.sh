#!/usr/bin/env bash
set -euo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  echo "[docker-install] Root yetkisi gerekiyor."
  echo "[docker-install] Kullanım: sudo bash script/shell/install_docker_ubuntu.sh"
  exit 1
fi

echo "[docker-install] Ubuntu Docker Engine kurulumu başlıyor..."

apt-get update
apt-get install -y ca-certificates curl gnupg lsb-release

install -m 0755 -d /etc/apt/keyrings
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | gpg --dearmor -o /etc/apt/keyrings/docker.gpg
chmod a+r /etc/apt/keyrings/docker.gpg

echo \
  "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu \
  $(. /etc/os-release && echo \"$VERSION_CODENAME\") stable" \
  > /etc/apt/sources.list.d/docker.list

apt-get update
apt-get install -y docker-ce docker-ce-cli containerd.io docker-buildx-plugin docker-compose-plugin

systemctl enable docker
systemctl start docker

# Current non-root user (if launched via sudo)
if [[ -n "${SUDO_USER:-}" ]]; then
  usermod -aG docker "${SUDO_USER}"
  echo "[docker-install] '${SUDO_USER}' kullanıcısı docker grubuna eklendi."
  echo "[docker-install] Grup değişikliği için oturumu kapat/aç veya: newgrp docker"
fi

echo "[docker-install] Kurulum tamamlandı."
echo "[docker-install] Test: docker --version && docker run --rm hello-world"

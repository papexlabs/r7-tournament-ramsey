#!/bin/bash
# EC2 user-data (runs once as root at first boot, Ubuntu 24.04 arm64).
# 1. Arms the hard stop FIRST: the instance powers off (and, launched with
#    --instance-initiated-shutdown-behavior terminate, is terminated) after
#    @@SHUTDOWN_MIN@@ minutes whatever happens.
# 2. Installs build tools and builds pinned CaDiCaL 3.0.1 and nauty 2.9.3 from
#    source (sha256-checked), the versions used on the Mac.
# 3. Writes /opt/tr-tools/READY when done (scripts/cloud/setup.sh waits for it).
# No credentials, no personal data; downloads use a generic User-Agent.
set -euxo pipefail
shutdown -h +@@SHUTDOWN_MIN@@ "tournament-ramsey hard stop"
exec > /var/log/tr-user-data.log 2>&1
export DEBIAN_FRONTEND=noninteractive
apt-get -qq update
apt-get -qq install -y build-essential git rsync python3 curl > /dev/null
UA='PapexResearchBot/1.0 (+https://papex.org)'
mkdir -p /opt/tr-tools/src && cd /opt/tr-tools/src
curl -fsSL -A "$UA" -o cadical.tgz https://github.com/arminbiere/cadical/archive/refs/tags/rel-3.0.1.tar.gz
echo "0a8ea563b5a25f5aa064634814edab45cc0e45111ea0f5d412a565f806fd7e11  cadical.tgz" | sha256sum -c -
curl -fsSL -A "$UA" -o nauty.tgz https://pallini.di.uniroma1.it/nauty2_9_3.tar.gz \
  || curl -fsSL -A "$UA" -o nauty.tgz https://users.cecs.anu.edu.au/~bdm/nauty/nauty2_9_3.tar.gz
echo "9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b  nauty.tgz" | sha256sum -c -
tar xzf cadical.tgz && tar xzf nauty.tgz
(cd cadical-rel-3.0.1 && ./configure > /dev/null && make -s -j"$(nproc)" > /dev/null)
install -m 755 cadical-rel-3.0.1/build/cadical /usr/local/bin/cadical
install -m 644 cadical-rel-3.0.1/build/libcadical.a /usr/local/lib/libcadical.a
install -m 644 cadical-rel-3.0.1/src/cadical.hpp /usr/local/include/cadical.hpp
(cd nauty2_9_3 && ./configure > /dev/null && make -s -j"$(nproc)" > /dev/null)
for b in labelg gentourng dretog; do install -m 755 nauty2_9_3/$b /usr/local/bin/$b; done
# open-file limit for many solver/checker pipes (kobon lesson: EMFILE at 180 workers)
echo "* soft nofile 65536" >> /etc/security/limits.conf
echo "* hard nofile 65536" >> /etc/security/limits.conf
cadical --version > /opt/tr-tools/READY

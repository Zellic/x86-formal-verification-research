#!/usr/bin/env bash
# Prepare the exact library archive read by this release's statements.
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
package='libc6-dev'
version='2.43-2ubuntu2.4'
architecture='amd64'
# Publisher: confirm both values with tools/release-confirm-libc.sh before publication.
DEB_URL='https://launchpadlibrarian.net/875753672/libc6-dev_2.43-2ubuntu2.4_amd64.deb'
DEB_SHA256='17bb816a65a25c3416854eef7e9cc6d9a3761f45bad0d44e49bc676b7bab1769'
LIBC_SHA256='2a277b999268f100c5f838689704b7432e9b1fdac76bf0cbda83cdbbaecc89e2'
relative='glibc-2.43-ubuntu-26.04-amd64/libc.a'

fail() { printf 'get-libc: %s\n' "$*" >&2; exit 1; }
verify() {
  local actual
  actual=$(sha256sum -- "$1")
  actual=${actual%% *}
  [ "$actual" = "$2" ] || fail "SHA-256 mismatch for $1 (expected $2, got $actual)"
}
need_package_hash() {
  [[ "$DEB_SHA256" =~ ^[0-9a-f]{64}$ ]] ||
    fail 'the package checksum is UNCONFIRMED; the publisher must confirm it before downloading'
}
mode=${1:-download}
case "$mode" in
  download) [ "$#" = 0 ] || fail 'usage: bash get-libc.sh [--archive libc.a | --deb package.deb]'
    need_package_hash
    [[ "$DEB_URL" =~ ^https://launchpadlibrarian\.net/[0-9]+/libc6-dev_2\.43-2ubuntu2\.4_amd64\.deb$ ]] ||
      fail 'the permanent package URL is UNCONFIRMED' ;;
  --archive|--deb) [ "$#" = 2 ] || fail 'supply exactly one input file'
    [ -f "$2" ] || fail "input file missing: $2"
    [ "$mode" != --deb ] || need_package_hash ;;
  *) fail 'usage: bash get-libc.sh [--archive libc.a | --deb package.deb]' ;;
esac
mkdir -p -- "$here/$(dirname -- "$relative")"
work=$(mktemp -d "$here/$(dirname -- "$relative")/.get-libc.XXXXXX")
trap 'rm -rf -- "$work"' EXIT
if [ "$mode" = --archive ]; then
  cp -- "$2" "$work/libc.a"
else
  if [ "$mode" = download ]; then
    curl --fail --location --max-time 300 --output "$work/package.deb" "$DEB_URL"
    deb="$work/package.deb"
  else
    cp -- "$2" "$work/package.deb"
    deb="$work/package.deb"
  fi
  verify "$deb" "$DEB_SHA256"
  [ "$(dpkg-deb --field "$deb" Package)" = "$package" ] || fail 'unexpected package name'
  [ "$(dpkg-deb --field "$deb" Version)" = "$version" ] || fail 'unexpected package version'
  [ "$(dpkg-deb --field "$deb" Architecture)" = "$architecture" ] || fail 'unexpected package architecture'
  dpkg-deb --fsys-tarfile "$deb" | tar -xOf - ./usr/lib/x86_64-linux-gnu/libc.a > "$work/libc.a"
fi
verify "$work/libc.a" "$LIBC_SHA256"
mv -f -- "$work/libc.a" "$here/$relative"
printf 'get-libc: verified %s  %s\n' "$LIBC_SHA256" "$relative"

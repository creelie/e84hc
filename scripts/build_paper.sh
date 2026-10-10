#!/usr/bin/env bash
# Build the paper and its three release files in dist/:
#   <name>.pdf            the compiled paper
#   <name>-tex.zip        LaTeX source, bibliography and figures (PNG, with
#                         their TikZ sources)
#   <name>-arxiv.tar.gz   what arXiv needs: main.tex, sections/, main.bbl and
#                         the PNG figures; compiled here with pdflatex alone
#                         as a test before it is written
# Needs pdflatex, bibtex, zip and tar.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
P="$ROOT/paper"
DIST="$ROOT/dist"
NAME="on-the-hodge-conjecture-for-fermat-varieties"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

latex() { pdflatex -interaction=nonstopmode -halt-on-error main.tex > /dev/null; }
settle() {  # run pdflatex until the cross-references stop changing
    for _ in 1 2 3 4; do
        latex
        grep -qE "Rerun to get|Label\(s\) may have changed" main.log || return 0
    done
    echo "FAIL  cross-references did not settle in $(pwd)"; exit 1
}
check_log() {  # check_log <dir>
    if grep -nE "^!|undefined|multiply defined" "$1/main.log"; then
        echo "FAIL  LaTeX reported errors or undefined references in $1"; exit 1
    fi
}

echo "== compile"
cd "$P"
rm -f main.aux main.bbl main.blg main.out
latex; bibtex main > /dev/null; settle
check_log "$P"
echo "ok    main.pdf, $(pdfinfo main.pdf 2>/dev/null | awk '/^Pages/{print $2}') pages"

mkdir -p "$DIST"
cp main.pdf "$DIST/$NAME.pdf"

echo "== arXiv tarball"
A="$TMP/arxiv"
mkdir -p "$A/sections" "$A/figures"
cp main.tex main.bbl "$A/"
cp sections/*.tex "$A/sections/"
cp figures/*.png "$A/figures/"
(cd "$A" && tar czf "$DIST/$NAME-arxiv.tar.gz" main.tex main.bbl sections figures)
T="$TMP/arxiv-test"
mkdir -p "$T" && tar xzf "$DIST/$NAME-arxiv.tar.gz" -C "$T"
(cd "$T" && settle)
check_log "$T"
echo "ok    arXiv tarball compiles with pdflatex alone"

echo "== tex.zip"
Z="$TMP/tex"
mkdir -p "$Z/sections" "$Z/figures/src"
cp main.tex main.bbl references.bib "$Z/"
cp sections/*.tex "$Z/sections/"
cp figures/*.png "$Z/figures/"
cp figures/src/*.tex "$Z/figures/src/"
cat > "$Z/README.txt" <<'TXT'
On the Hodge conjecture for Fermat varieties  (Deep Bhattacharjee)

Build:  pdflatex main && bibtex main && pdflatex main && pdflatex main
The figures are PNG files in figures/.  Their TikZ sources are in
figures/src/; each compiles with pdflatex and is converted with
pdftoppm -r 300 -png -singlefile fig_X.pdf ../fig_X
TXT
rm -f "$DIST/$NAME-tex.zip"
(cd "$Z" && zip -qr "$DIST/$NAME-tex.zip" .)
echo "ok    tex.zip with $(unzip -l "$DIST/$NAME-tex.zip" | grep -c '\.png$') PNG figures"

ls -l "$DIST"

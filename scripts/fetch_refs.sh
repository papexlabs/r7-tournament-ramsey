#!/bin/bash
# Re-download the third-party sources used by the experiments (not redistributed here).
# Generic User-Agent, no credentials.
set -euo pipefail
cd "$(dirname "$0")/../refs"
UA='PapexResearchBot/1.0 (+https://papex.org)'
curl -sSL -A "$UA" -o 2011.00683v2.pdf https://arxiv.org/pdf/2011.00683v2
curl -sSL -A "$UA" -o FMCAD22-lohn-lambert-heule.pdf https://www.cs.cmu.edu/~mheule/publications/FMCAD22.pdf
mkdir -p directed-ramsey-src digraph-isolators-src
curl -sSL -A "$UA" -o directed-ramsey-src/repo.tar.gz https://codeload.github.com/neimandavid/Directed-Ramsey/tar.gz/refs/heads/master
curl -sSL -A "$UA" -o digraph-isolators-src/repo.tar.gz https://codeload.github.com/evanlohn/digraph_isolators/tar.gz/HEAD
(cd directed-ramsey-src && tar xzf repo.tar.gz)
(cd digraph-isolators-src && tar xzf repo.tar.gz)
shasum -a 256 2011.00683v2.pdf FMCAD22-lohn-lambert-heule.pdf \
  digraph-isolators-src/digraph_isolators-HEAD/tt6free_tournaments/*.d6

# ./start-ide.sh
stack hoogle --rebuild
stack hoogle --server 2> /dev/null 1> /dev/null &
(stack exec ghcid -- \
  --command 'stack repl --ghc-options "-fno-code -ignore-dot-ghci -ferror-spans"' \
  --test ':! stack exec hasktags -- --ctags . && stack hoogle -- generate --local ${your_package_name}' \
  --warnings \
  --outputfile ghcid.txt) || true
(pkill ghcid && echo "Killed Ghcid.") || echo "No Ghcid process to kill."
(pkill hoogle && echo "Killed Hoogle.") || echo "No Hoogle process to kill."

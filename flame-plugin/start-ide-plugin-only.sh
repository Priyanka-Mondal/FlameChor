# ./start-ide.sh
stack --stack-yaml stack-debug.yaml hoogle --rebuild
stack --stack-yaml stack-debug.yaml hoogle --server 2> /dev/null 1> /dev/null &
(stack --stack-yaml stack-debug.yaml exec ghcid -- \
  --command 'stack --stack-yaml stack-debug.yaml repl --ghc-options "-fno-code -ignore-dot-ghci -ferror-spans"' \
  --test ':! stack --stack-yaml stack-debug.yaml exec hasktags -- --ctags . && stack --stack-yaml stack-debug.yaml hoogle -- generate --local ${your_package_name}' \
  --warnings \
  --outputfile ghcid.txt) || true
(pkill ghcid && echo "Killed Ghcid.") || echo "No Ghcid process to kill."
(pkill hoogle && echo "Killed Hoogle.") || echo "No Hoogle process to kill."

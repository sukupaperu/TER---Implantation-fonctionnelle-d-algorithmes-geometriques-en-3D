if [ "$1" = "clear" ]; then
    rm -f *.vo *.vos *.vok *.aux *.glob
    rm -r haskell
    echo "Done."
elif [ "$1" = "build" ]; then
    mkdir -p haskell
    coqc _3d_trigo.v
    coqc global_v_list.v
    coqc test.v
    echo "Done."
else
    echo "Unknown command"
fi
# ghc -o haskell/test haskell/test.hs
if [ "$1" = "clear" ]; then
    rm -f *.vo *.vos *.vok *.aux *.glob .*.aux
    rm -f haskell/*.hi haskell/*.o
    rm -f haskell/Main haskell/Extracted.hs
    echo "Done."
elif [ "$1" = "build" ]; then
    mkdir -p haskell
    coqc _3d_trigo.v
    coqc global_v_list.v
    coqc test.v
    echo "Done."
elif [ "$1" = "build_h" ]; then
    cd haskell
    ghc --make Main.hs
    echo "Done."
else
    echo "Unknown command"
fi
# ghc -o haskell/test haskell/test.hs
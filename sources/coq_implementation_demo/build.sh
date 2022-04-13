if [ "$1" = "clear" ]; then
    rm -f *.vo *.vos *.vok *.aux *.glob .*.aux
    rm -f haskell/*.hi haskell/*.o
    rm -f haskell/Main haskell/Extracted.hs
    echo "Done."
elif [ "$1" = "build" ]; then
    mkdir -p haskell
    coqc trigo_3d.v
    coqc other_structures.v
    coqc quickhull_3d.v
    coqc test.v
    echo "Done."
elif [ "$1" = "test" ]; then
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
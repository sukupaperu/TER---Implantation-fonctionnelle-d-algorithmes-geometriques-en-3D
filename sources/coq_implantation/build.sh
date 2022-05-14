if [ "$1" = "clear" ]; then
    rm -f *.vo *.vos *.vok *.aux *.glob .*.aux *.conf makefile .*.d
    rm -f haskell/*.hi haskell/*.o
    rm -f haskell/Main haskell/Extracted.hs
    echo "Done."
elif [ "$1" = "makefile" ]; then
    mkdir -p haskell
    coq_makefile ./*.v > makefile
    echo "Done."
elif [ "$1" = "haskell" ]; then
    cd haskell
    # -02 pour une compilation plus lente mais avec plus d'optimiations
    ghc -O2 --make Main.hs
    echo "Done."
else
    echo "Unknown command"
fi
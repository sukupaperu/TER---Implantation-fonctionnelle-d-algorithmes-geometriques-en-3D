# Implantation Coq avec extraction en Haskell
## Compilation et exécution
Génération du fichier `makefile` pour l'environnement de compilation Coq :
- `./build.sh makefile`

Compilation des fichiers source Coq et extraction des fichiers haskell :
- `make -j4`

Compilation des fichiers source Haskell :
- `./build.sh haskell`

Exécution de l'exécutable généré :
- `./haskell/Main`

### En une seule commande :
- `./build.sh makefile && make -j4 && ./build.sh haskell`
- `./haskell/Main`
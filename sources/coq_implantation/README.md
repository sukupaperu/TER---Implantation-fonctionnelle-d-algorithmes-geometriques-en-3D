# Implantation Coq avec extraction en Haskell
Une implantation en Coq de la première étape de l'algorithme Quickhull.
Ce programme ne fait donc que calculer l'enveloppe convexe 3D initiale (nécessaire à Quickhull) à partir d'un ensemble de points 3D donné en entrée. L'objet obtenu en sortie doit donc être un tétrahèdre (soit une liste de 3x4 indices de sommets, à condition qu'il n'y ait pas d'erreur à l'exécution).

## Compilation
On génère d'abord le fichier `makefile` nécessaire à la compilation des fichiers de code source Coq :
- `./build.sh makefile`

On compile ensuite le code source Coq, ce qui conduit à l'extraction de code source Haskell (dans le dossier haskell) :
- `make -j4`

Dernière étape où cette fois-ci c'est le code source Haskell qui est compilé :
- `./build.sh haskell`
Ce qui produit alors l'exécutable `haskell/Main`.

### En une seule commande :
- `./build.sh makefile && make -j4 && ./build.sh haskell`

### Nettoyage
- `./build.sh clear`

## Usage
On se déplace dans le bon répertoire :
- `cd haskell`

On exécute le programme en lui passant en entrée une liste de sommets, tout en redirigeant le flux de sortie du programme vers un fichier contenant la liste des indices des faces :
- `./Main <fichier_liste_de_sommets> > <fichier_liste_de_faces>`

Pour visualiser le fichier obtenu, on peut se servir du `viewer` :
- `./viewer <fichier_liste_de_sommets> <fichier_liste_de_faces>`

### En une seule commande :
- `./Main VertexList.txt > FaceList.txt && ./viewer VertexList.txt FaceList.txt`
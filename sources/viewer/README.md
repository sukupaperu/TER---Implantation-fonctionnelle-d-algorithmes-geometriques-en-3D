# Viewer
Un visualiseur 3D simpliste de de points et de faces reliant ces points. l'intérieur des faces apparait en gris, l'extérieur en bleu. Les points appartenant à ces faces sont affichés en rouge.

## Compilation
- `make`

## Usage
- `./viewer <fichier_liste_de_sommets> <fichier_liste_de_faces>`

Ou si on ne souhaite pas charger de faces :
- `./viewer <fichier_liste_de_sommets>`

Avec la touche espace on peut basculer dans 4 différents modes de visualisation.

## Détail des fichiers d'entrée
Un `<fichier_liste_de_sommets>` est une liste triplets de nombre flottants représentant les coordonnées x, y et z des points à afficher. Un fichier valide a autant de lignes de triplets qu'il n'y a de points à afficher, et la dernière ligne doit être vide.
Exemple :
```-0.46404988816647796 0.17169445096526037 -0.24371578569708977
-0.5231352212964112 0.36481086782731076 0.7131271321823632
0.5032582294218616 0.2884301680651348 -0.30269132725441605
0.5361247092912445 -0.5675183355803073 0.09773051790095974
0.6551749196143297 0.41717907053893044 0.5847958234985875

```

Un fichier `<fichier_liste_de_faces>` est une liste de d'indice de sommet faisant directement référence au fichier précédent.
Les indices sont lus par groupe de 3 pour former les triangles à afficher (à noter que les triangles sont orientés).
Un fichier valide est un fichier dans lequel chaque ligne correspond à un entier positif compris dans l'intervalle d'indices de sommets possibles, et comportant un nombre d'indices multiple de 3. Ici aussi la dernière ligne doit être laissée vide.
Exemple :
```
161
30
232
232
30
217
30
161
217
161
232
217

```

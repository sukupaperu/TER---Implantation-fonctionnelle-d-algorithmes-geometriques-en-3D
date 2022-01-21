"use strict";

// ------------- Fonctions trigonométriques -------------

/*
	Diverses opérations sur les sommets/vecteurs
*/
// u - v
const minus = (u,v) =>
    vertex_3d(u.x - v.x, u.y - v.y, u.z - v.z);
// ||v||
const norm = v =>
    (v.x*v.x + v.y*v.y + v.z*v.z);

/*
	Calcule le rejet scalaire du vecteur u sur le vecteur v.
	Formule tirée de : https://en.wikipedia.org/wiki/Vector_projection#Scalar_rejection
*/
const vector_reject_2d = (u, v) =>
    (u.y*v.x - u.x*v.y);

/*
	Considérant une droite passant par a et b, renvoie la distance minimale entre cette droite et la point c.
*/
const dist_from_segment = (a, b, c) =>
    vector_reject_2d(minus(c,a), minus(b,a));
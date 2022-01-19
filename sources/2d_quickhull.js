"use strict";

// ------------- Algorithme Quickhull -------------

const quick_hull_2d_rec = (indices_list, left, right) =>
{
	if(indices_list.length === 0)
	{
		// Si la liste est vide, alors aucun point supplémentaire ne peut faire partie de l'enveloppe convexe
		return [];
	}
	else
	{
		// On récupère dans la liste le point le plus éloigné du segment left-right
		const furthest = reduce_list(indices_list,
			bool_reducer(
				(c1,c2) =>
					dist_from_segment(V(left), V(right), V(c1)) 
					> dist_from_segment(V(left), V(right), V(c2))
			)
		);

		// On créé une nouvelle liste qui ne contient pas ce point
		const new_indices_list = filter_list(indices_list, (u) => u !== furthest);

		// console.log(
		// 	"furthest:",furthest,
		// 	"\nlist:",new_indices_list,
		// 	"\nlist_l:",filter_list(new_indices_list, 
		// 		(c) => dist_from_segment(V(left), V(furthest), V(c)) >= 0
		// 	),
		// 	"\nlist_r:",filter_list(new_indices_list, 
		// 		(c) => dist_from_segment(V(furthest), V(right), V(c)) >= 0
		// 	)
		// )

		return [].concat(
			// On calcule les points situés à gauche du segment left-furthest faisant partie de l'env. convexe
			quick_hull_2d_rec(
				filter_list(new_indices_list, 
					(c) => dist_from_segment(V(left), V(furthest), V(c)) >= 0
				),
				left, furthest
			),
			// On calcule les points situés à gauche du segment furthest-right faisant partie de l'env. convexe
			quick_hull_2d_rec(
				filter_list(new_indices_list, 
					(c) => dist_from_segment(V(furthest), V(right), V(c)) >= 0
				),
				furthest, right
			),
			// On ajoute le point retiré précédemment
			furthest
		);
	}
};

const quick_hull_2d = (vertex_list) =>
{
    // À partir de la liste de sommets, on créé une liste d'indices leur faisant référence
	const indices_list = new_ordered_int_list(vertex_list.length);

	// On récupère dans la liste le point situé le plus à gauche
	const left = reduce_list(indices_list,
		bool_reducer((u,v) => V(u).x < V(v).x)
	);

	const indices_list_wo_left = filter_list(indices_list, (u) => u !== left);

	// On récupère dans la liste le point situé le plus à droite
	const right = reduce_list(indices_list_wo_left,
		bool_reducer((u,v) => V(u).x > V(v).x)
	);

	// On créé une nouvelle liste qui ne contient pas ces deux points
	const indices_list_wo_left_right = filter_list(indices_list_wo_left, (u) => u !== right);
    
	return [].concat(
		// On calcule les points situés à gauche du segment left-right faisant partie de l'env. convexe
		quick_hull_2d_rec(
			filter_list(indices_list_wo_left_right, 
				(c) => dist_from_segment(V(left), V(right), V(c)) >= 0
			),
			left,
			right
		),
		// On calcule les points situés à droite du segment left-right faisant partie de l'env. convexe
		quick_hull_2d_rec(
			filter_list(indices_list_wo_left_right, 
				(c) => dist_from_segment(V(left), V(right), V(c)) < 0
			),
			right,
			left
		),
		// On ajoute les points retirés précédemment
		left,
		right
	);
};
// ------------- fin Algorithme Quickhull -------------
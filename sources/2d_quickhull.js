"use strict";

// ------------- Algorithme Quickhull -------------

const quick_hull_2d_rec = (indices_list, V, left, right) =>
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

		disp.push_indices([left, right]);
		disp.push_indices([left, furthest, right]);

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
					(c) => dist_from_segment(V(left), V(furthest), V(c)) > 0
				), V,
				left, furthest
			),
			// On ajoute le point retiré précédemment
			furthest,
			// On calcule les points situés à gauche du segment furthest-right faisant partie de l'env. convexe
			quick_hull_2d_rec(
				filter_list(new_indices_list, 
					(c) => dist_from_segment(V(furthest), V(right), V(c)) >= 0
				), V,
				furthest, right
			)
		);
	}
};

const quick_hull_2d = (vertex_list) =>
{
    // À partir de la liste de sommets, on créé une liste d'indices leur faisant référence
	const indices_list = new_ordered_int_list(vertex_list.length);
	const V = (index) => vertex_list[index];

	// On récupère dans la liste le point situé le plus à gauche
	const left = reduce_list(indices_list,
		bool_reducer((u,v) => V(u).x < V(v).x)
	);
	// On créé une nouvelle liste qui ne contient pas le point left
	const indices_list_wo_left = filter_list(indices_list, (u) => u !== left);

	// On récupère dans la liste le point situé le plus à droite
	const right = reduce_list(indices_list_wo_left,
		bool_reducer((u,v) => V(u).x > V(v).x)
	);

	// On créé une nouvelle liste qui ne contient pas le point right
	const indices_list_wo_left_right = filter_list(indices_list_wo_left, (u) => u !== right);
    
	return [].concat(
		// On ajoute les point left (retiré précédemment)
		left,
		// On calcule les points situés à gauche du segment left-right faisant partie de l'env. convexe
		quick_hull_2d_rec(
			filter_list(indices_list_wo_left_right, 
				(c) => dist_from_segment(V(left), V(right), V(c)) >= 0
			), V,
			left, right
		),
		// On ajoute les point right (retiré précédemment)
		right,
		// On calcule les points situés à droite du segment left-right faisant partie de l'env. convexe
		quick_hull_2d_rec(
			filter_list(indices_list_wo_left_right, 
				(c) => dist_from_segment(V(left), V(right), V(c)) < 0
			), V,
			right, left
		)
	);
};
// ------------- fin Algorithme Quickhull -------------
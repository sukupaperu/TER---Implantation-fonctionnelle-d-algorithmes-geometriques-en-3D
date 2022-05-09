"use strict";

// ---- Opérations sur les listes ----

// int -> int list
const new_ordered_int_list = (n) =>
	n === 0
		? []
		: n === 1
			? [0]
			: new_ordered_int_list(n - 1).concat(n - 1)
	;

// ---- Opérations sur les listes (ici volontairement en approche non-fonctionnelles) ----

// () -> any list
const new_empty_list = () =>
	[]
	;

// any list -> int
const list_length = (list) =>
	list.length
	;

// any list -> int -> any
const value_in_list_by_index = (list, index) =>
	list[index]
	;

// any list -> bool
const list_is_empty = (list) =>
	list_length(list) === 0
	;

// ---- Fonctions diverses ----

// (any -> any -> bool) -> (any -> any) -> any
const first_arg_if_true = condition =>
	(a, b) => condition(a, b) ? a : b
	;

// any -> bool
const is_defined = (a) =>
	a !== undefined
	;

const V = (index) =>
	value_in_list_by_index(GLOBAL_V_LIST, index);
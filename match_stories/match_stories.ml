open Printf

module KI = Utilities.S.PH.B.PB.CI.Po.K
module IntMap = Map.Make(struct type t = int let compare = compare end)

(****************************************************************************
* General map helpers 
*)
let map_add_val_to_list map key v = 
	if (IntMap.mem key map) then
		let val_list = IntMap.find key map in 
			IntMap.add key (val_list @ [v]) map
	else IntMap.add key [v] map

let map_rem_head_from_list map key = 
	if IntMap.mem key map then
		let val_list = IntMap.find key map in 
			if (List.length val_list) = 1 then
				IntMap.remove key map
			else
				IntMap.add key (List.tl val_list) map
	else map

(****************************************************************************
* Story data structures 
*)
type instantiation_t = Instantiation.concrete Instantiation.event

module StoryEvent =
	struct
		type t = (int * (int * instantiation_t))

		let compare (x: t) y = 
			match (x, y) with 
			| ((x1, _), (y1, _)) -> (
	 			if (x1 < y1) then -1
				else if (x1 > y1) then 1
				else 0
			)
	end;;

(* adjacency_list_t : int -> [StoryEvent] *)
type adjacency_list_t = (StoryEvent.t list) IntMap.t 
type story_t = (adjacency_list_t * adjacency_list_t) * (StoryEvent.t list)

(**************************************************************************
* Create test story. This is a hack. Eventually we will read this 
* from user input depending on the story the user is searching for.
*)
let find_id_for_rule env name = 
	(* Environment.num_of_rule (Location.dummy_annot name) env *)
	1

let find_all_applications env steps = 
	let map = IntMap.empty in 
	let find_application env map step = 
		match step with
		| KI.Event ((Causal.RULE (rule)), inst) ->
				map_add_val_to_list map rule inst
		| KI.Event _ | KI.Subs _ | KI.Dummy _ | KI.Obs _ | KI.Init _ -> map
	in
	List.fold_left (find_application env) map steps 

(* TODO: Change x, y below...figure out how we are id'ing elements. *)
let create_toy_story env steps = 
	let get_rand_element l = List.nth l (Random.int (List.length l)) in
	let map = find_all_applications env steps in (* Need to handle if x not in map *)
	let x_id = (find_id_for_rule env "x") in
	let y_id = (find_id_for_rule env "y") in
	let x_event : StoryEvent.t = 
		(0, (x_id, get_rand_element (IntMap.find x_id map))) in 
	let y_event : StoryEvent.t = 
		(1, (y_id, get_rand_element (IntMap.find y_id map))) in
	let forward_list : adjacency_list_t = IntMap.singleton 0 [y_event] in
	let reverse_list : adjacency_list_t = IntMap.singleton 1 [x_event] in
	let start_events = [x_event] in
	((forward_list, reverse_list), start_events)


(******************************************************************************
* Weak compression matching helpers and algorithm 
*)
let mark_steps_with_id steps = 
	let add_id id_list step = 
		if ((List.length id_list) = 0) then [(0, step)]
		else
			let (cur_int, _) = List.hd id_list in
			([(cur_int + 1, step)] @ id_list) 
	in
	List.fold_left add_id [] steps

let add_story_events_to_map map story_events = 
	let add_story_event_to_map map story_event = 
		let (_, (rule, _)) = story_event in
		map_add_val_to_list map rule story_event
	in 
	List.fold_left add_story_event_to_map map story_events

let step_weak_algorithm (s : story_t) (wq, result_map, is_done) mark_step = 
	if is_done then (wq, result_map, is_done)
	else 
		let (step_id, step) = mark_step in
		let ((forward_edges, backward_edges), _) = s in
		match step with
		| KI.Event (Causal.RULE (rule), trace_inst) -> (
			if IntMap.mem rule wq then (
				let filtered = 
					List.filter 
						(fun ((_, (_, story_inst)) : StoryEvent.t) -> (story_inst = trace_inst)) 
						(IntMap.find rule wq) in
				if ((List.length filtered) > 0) then (  
					(* Here we've matched trace event to a story event *)
					let (story_event_id, (rule_id, story_inst)) = List.hd filtered in
					(* Update result set with new mapping *)
					let result_map = IntMap.add story_event_id step_id result_map in
					(* Remove matched story instance from wq *)
					let wq = map_rem_head_from_list wq rule in
					(* Add new elements from story to wq *)
					let might_add = IntMap.find story_event_id forward_edges in
					(* Only add if all predecessors have been handled *)
					let all_pred_handled ((story_event_id, _) : StoryEvent.t) = (
						let pred_handled prev_handled (pred_id, _) = 
							(prev_handled && (IntMap.mem pred_id result_map))
						in
						List.fold_left pred_handled true (IntMap.find story_event_id backward_edges)
					) in
					let to_add = List.filter all_pred_handled might_add in
					let wq = add_story_events_to_map wq to_add in
					(wq, result_map, IntMap.is_empty wq)
				)
				else (wq, result_map, is_done)  (* No matching instantiation *)
			)
			else (wq, result_map, is_done)  (* No matching rule *)
			)
		| KI.Event _ | KI.Dummy _ | KI.Obs _ | KI.Init _ | KI.Subs _ -> 
			(wq, result_map, is_done)

(* Does OCaml have a HashMap implementation? Otherwise, consider using HashTbl
 * when possible, because these are log n lookups. *)
let check_weak_story_embeds env steps = 
	let s = (create_toy_story env steps) in
	let ((_, _), start_events) = s in
	let wq = IntMap.empty in (* wq is map from rule id to story_events *)
	let result_map = IntMap.empty in (* result_map maps story_event ids to trace id *)
	let wq = add_story_events_to_map wq start_events in (* Initialize wq *)
	let param = (wq, result_map, false) in
	let (_, _, is_done) = 
		List.fold_left (step_weak_algorithm s) param (mark_steps_with_id steps)
	in
	if is_done then (printf "%s " "matches")
	else (printf "%s " "doesn't match") 

(***********************************************************************
* Printing traces for debugging
*)
let print_trace env steps = 
  Format.eprintf "@[<v>%a@]" (Pp.list Pp.space KI.print_refined_step) steps

let print_rule env f step = 
	match step with 
	| KI.Event (event_kind, _) ->
		(
			match event_kind with
			| Causal.RULE (rule) ->
				Environment.print_rule ~env:env Format.err_formatter rule
			| Causal.OBS _ | Causal.INIT _ | Causal.PERT _ -> ()
		) 
	| KI.Subs _ | KI.Dummy _ | KI.Obs _ | KI.Init _ -> ()

let print_rules env steps =
	Format.eprintf "@[<v>%a@]" (Pp.list Pp.space (print_rule env)) steps
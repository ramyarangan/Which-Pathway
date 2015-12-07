 
module KI = Utilities.S.PH.B.PB.CI.Po.K

module IntMap = Map.Make(struct type t= int let compare = compare end);;

type instantiation = Instantiation.concrete Instantiation.event

module StoryEvent =
	struct
		type story_event = (int * (int * instantiation))

		let compare (x: story_event) y = 
			match (x, y) with 
			| ((x1, _), (y1, _)) -> (
	 			if (x1 < y1) then -1
				else if (x1 > y1) then 1
				else 0
			)
	end;;

(* adjacency_list : StoryEvent -> [StoryEvent] *)

type adjacency_list = (StoryEvent.t list) Map.Make(StoryEvent).t 
type story = adjacency_list * adjacency_list * (StoryEvent.story_event list)

(* Create a toy story. This is a hack, eventually we will read this from user input 
* depending on the story the user is searching for.
*)

(* all_applications : int -> [instantiation] *)
type all_applications = (instantiation list) IntMap.t

let map_add_val_to_list map key val = 
	if Map.mem key map then
		let val_list = Map.find key map in 
			map = Map.add key (val_list @ [val]) map
	else map = add key [val] map
	map

(* GET FROM PIERRE *)
let find_id_for_rule env name = 


let fill_all_applications env steps = 
	let map = all_applications.empty in 
	let fill_application env map step = 
		match step with
		| KI.Event ((Causal.RULE (rule)), inst) ->
				map_add_val_to_list map rule inst
		| KI.Event _ | KI.Subs _ | KI.Dummy _ | KI.Obs _ | KI.Init _ -> map
	in
	List.fold_left (fill_application env) map steps 


(* TODO: Change x, y below...figure out how we are id'ing elements. *)
let create_toy_story env steps = 
	let get_rand_element l = List.nth l (Random.int (List.length l)) in
	let map = find_all_applications env steps in (* Need to handle if x not in map *)
	let x_id = (find_id_for_rule env "x") in
	let y_id = (find_id_for_rule env "y") in
	let x_event : StoryEvent.story_event = 
		(0, x_id, get_rand_element (find x_id map)) in 
	let y_event : StoryEvent.story_event = 
		(1, y_id, get_rand_element (find y_id map)) in
	let forward_list : adjacency_list = Map.singleton x_event [y_event] in
	let reverse_list : adjacency_list = Map.singleton y_event [x_event] in
	let start_events = [x_event] in
	(forward_list, reverse_list, start_events)

(* FILL IN. Function to a bool *)
let instantiation_matches trace_inst story_inst = 
	
let mark_steps steps = 


(* Does OCaml have a HashMap implementation? Otherwise, consider using HashTbl
 * when possible, because these are log n lookups. *)
let story_embeds env steps story = 
	let (forward_list, reverse_list, start_events) = 
		(create_toy_story env steps) in
	let M = IntMap.empty in (* M is map from rule id to story_events *)
	let S = IntMap.empty in (* S is a map from story_event ids to trace id *)
	let add_event map story_event = 
		let (rule_id, (rule, instantiation)) = story_event in
		map_add_val_to_list M rule story_event
	in 
	let M = List.fold_left add_event M start_events in (* Initialize M *)
	let step_algorithm result_map mark_step = 
		let (step, step_id) = mark_step in
		match step with
		| KI.Event (Causal.RULE (rule), trace_inst) -> (
			if Map.mem rule M then (
				let filtered = 
					List.filter (instantiation_matches trace_inst) (Map.find rule M) in
				if not filtered.is_empty then (
					let (story_event_id, (rule_id, story_inst)) = List.hd filtered in (
						let S = S.add story_event_id step_id S 
					)
				)
			)
			)
		| KI.Event _ | KI.Dummy _ | KI.Obs _ | KI.Init _ -> (* do this *)
	in 
	S = List.fold_left (step_algorithm S) (mark_steps steps)
(*********************************************************************
* Printing traces for debugging
*
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
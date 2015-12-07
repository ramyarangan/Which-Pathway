 
module KI = Utilities.S.PH.B.PB.CI.Po.K

type instantiation = Instantiation.concrete Instantiation.event

module StoryEvent =
	struct
		type story_event = (int * (string * instantiation))

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
type all_applications = instantiation Map.Make(int).t

let map_add_val_to_list map key val = 
	if Map.mem key map then
		let val_list = Map.find key map in 
			map = Map.add key (val_list @ [val]) map
	else map = add key [val] map
	map


let fill_all_applications env steps = 
	let map = all_applications.empty in 
	let fill_application env map step = 
		match step with
		| KI.Event ((Causal.RULE (rule)), inst) ->
				map_add_val_to_list map rule inst
		| KI.Event _ | KI.Subs _ | KI.Dummy _ | KI.Obs _ | KI.Init _ -> map
	in
	List.fold_left (fill_application env) map steps 

let create_toy_story env steps = 
	let get_rand_element l = List.nth l (Random.int (List.length l)) in
	let map = find_all_applications env steps in (* Need to handle if x not in map *)
	let x_event : StoryEvent.story_event = 
		(0, "x", get_rand_element (find "x" map)) in 
	let y_event : StoryEvent.story_event = 
		(1, "y", get_rand_element (find "y" map)) in
	let forward_list : adjacency_list = Map.singleton x_event [y_event] in
	let reverse_list : adjacency_list = Map.singleton y_event [x_event] in
	let start_events = [x_event] in
	(forward_list, reverse_list, start_events)

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

let event_matches trace_step story_event = 
	

let add_event map story_event = 
	let (rule_id, (rule, instantiation)) = story_event in
	map_add_val_to_list M rule story_event

(* Does OCaml have a HashMap implementation? Otherwise, consider using HashTbl
 * when possible, because these are log n lookups. *)
let story_embeds env steps story = 
	let (forward_list, reverse_list, start_events) = 
		(create_toy_story env steps) in
	let M = (Map.Make(int)).empty in (* M is map from rule id to story_events *)
	let S = (Map.Make(int)).empty in (* S is a map from story_event ids to trace id *)
	
	(* Initialize the list M *)
	(* Hash table of M *)
	(* *)
	(* Can you get keySet for a map? *)
	()

	
(*  
* get sample story, build sample trace 
* *)
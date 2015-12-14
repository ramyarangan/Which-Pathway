(* Matching from a weakly compressed story to a trace, and
 * from a weakly compressed story with agent identifiers abstracted
 * away to a trace. 
 *
 * At the present, there is no easy user interface to check for 
 * story matching, as there is no format in which a user can
 * easily specify a story. In create_toy_story, we provide an example of 
 * checking weak compression story matching on a sample example
 * provided, in simple.ka.  
 *)
open Printf

module KI = Utilities.S.PH.B.PB.CI.Po.K
module IntMap = Map.Make(struct type t = int let compare = compare end)
module IntPairMap = Map.Make(struct type t = (int * int) let compare = compare end)

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

let mark_steps_with_id steps = 
	let add_id id_list step = 
		if ((List.length id_list) = 0) then [(0, step)]
		else
			let (cur_int, _) = List.hd id_list in
			([(cur_int + 1, step)] @ id_list) 
	in
	List.fold_left add_id [] steps

let map_rem_from_list_by_id map key n = 
	if IntMap.mem key map then
		let val_list = IntMap.find key map in 
			if (List.length val_list) < n then map
			else if (List.length val_list) = 1 then
				IntMap.remove key map
			else (
				let id_val_list = mark_steps_with_id val_list in
				let id_val_list = 
					List.filter (fun (id, _) -> (id <> n)) id_val_list in
				let get_first first_list new_val = (
					match new_val with
					| (_, add_val) -> first_list @ [add_val] 
				)
				in
				let val_list = 
					List.fold_left get_first [] id_val_list in
				IntMap.add key val_list map
			)
	else map

(****************************************************************************
* Story data structures
* Stories are graphs where nodes are story_events. 
* Story events are represented as a tuple: (unique id, (rule id, instantiation))
* Adjacency lists map a story's unique id to a list of the story_events
* it connects to.
* A story is represented by a tuple: 
* ((forward_edges, backward_edges), starting nodes)
* 
* Note: This structure is used to represent both strong and weakly compressed
* stories. In the matching process, the specific instantiation is not preserved
* for strongly compresssed stories, but distinct instantiations remain
* separate through the matching.
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
* Create test story for weakly compressed story matching algorithm.
* Eventually we will read this from user input depending on the story 
* the user is searching for. For now, there is no easy format for this
* user input.
*)
let find_id_for_rule env name = 
	let rule_id_list = Environment.nums_of_rule name env in
	if (List.length rule_id_list) = 0 then (
		printf "%s %s" "failed to find rule: " name;
		None
	)
	else (Some ((List.hd rule_id_list) + 1))

(* Creates a map linking a rule to all of its instantiations in a trace. 
 * This will be useful for creating a weakly compressed story for a particular
 * trace as a test. *)
let find_all_applications env steps = 
	let map = IntMap.empty in 
	let find_application env map step = 
		match step with
		| KI.Event ((Causal.RULE (rule)), inst) -> (	
				map_add_val_to_list map rule inst
		)
		| _ -> map
	in
	List.fold_left (find_application env) map steps 

(* Check for two neighboring events in our test story that the agents
 * affected by the first event's action are those that are tested 
 * by the second event. This creates a story that involves links
 * between the same instantiations of events. 
 *)
let check_test_action_matches env first_event second_event = 
	match (first_event, second_event) with
	| (_, (_, (_, (actions, _,_)))), (_, (_, (tests, _))) -> (
		let add_agents_to_list agent_list action = (
			match action with
			| Instantiation.Bind (((id_1, name_1), _), ((id_2, name_2), _)) -> (
				(agent_list @ [(id_1, name_1)]) @ [(id_2, name_2)]
			)
	  	| Instantiation.Bind_to (((id_1, name_1), _), ((id_2, name_2), _)) -> (
				(agent_list @ [(id_1, name_1)]) @ [(id_2, name_2)]
			)
	  	| _ -> agent_list
	  ) in
	  let filter_agents_by_match agent_list test = (
	  	match test with 
			| Instantiation.Is_Bound_to (((id_1, name_1), _), ((id_2, name_2), _)) -> (
				(List.mem (id_1, name_1) agent_list) && 
					(List.mem (id_2, name_2) agent_list)
			)
			| _ -> false
	  ) in
	  let agent_list = List.fold_left add_agents_to_list [] actions in
	  let filtered_tests = List.filter (filter_agents_by_match agent_list) tests in
	  (List.length filtered_tests) <> 0
	)

(* Creates a toy story for simple.ka *)
(* Here we show an example of creating a weakly compressed story for 
 * the set of rules outlined in simple.ka. 
 * We find the rule id corresponding to the events we would like to link, 
 * make sure that the instantiations of these rules are present in our
 * trace and correspond to the same agents, and finally create
 * the adjacency lists that specify a story. 
 *)
let create_toy_story env steps = 
	let get_rand_element l = List.nth l (Random.int (List.length l)) in
	let map = find_all_applications env steps in
	let x_id_option = (find_id_for_rule env "A.B") in
	let y_id_option = (find_id_for_rule env "AB.C") in
	match (x_id_option, y_id_option) with 
	| (Some x_id, Some y_id) -> (
		match ((IntMap.mem x_id map), (IntMap.mem y_id map)) with
		| (true, true) -> (
			let rec get_events () = (
				let x_event : StoryEvent.t = 
				(0, (x_id, get_rand_element (IntMap.find x_id map))) in 
				let y_event : StoryEvent.t = 
					(1, (y_id, get_rand_element (IntMap.find y_id map))) in
				if check_test_action_matches env x_event y_event then
					(x_event, y_event)
				else get_events ()
			) in
			let (x_event, y_event) = get_events () in 
			let forward_list : adjacency_list_t = IntMap.singleton 0 [y_event] in
			let reverse_list : adjacency_list_t = IntMap.singleton 1 [x_event] in
			let start_events = [x_event] in
			printf "Created test story A.B -> AB.C \n ";
			Some ((forward_list, reverse_list), start_events)
		)
		| _ -> None
	)
	| _ -> None

(******************************************************************************
* Algorithm for matching weakly compressed stories to a trace 
*)
let add_story_events_to_map map story_events = 
	let add_story_event_to_map map story_event = 
		let (_, (rule, _)) = story_event in
		map_add_val_to_list map rule story_event
	in 
	List.fold_left add_story_event_to_map map story_events

(*
 * For each event in the trace, update our map linking story events to their
 * counterparts in the trace. If the set of remaining events in the story that we
 * need to map (with current next steps represented in the work queue) is 
 * is empty, we mark our matching as done, which is passed on to runs of this
 * function on future steps of the trace.
 *)
let step_weak_algorithm (s : story_t) (wq, result_map, is_done) mark_step = 
	if is_done then (wq, result_map, is_done)
	else 
		let (step_id, step) = mark_step in
		let ((forward_edges, backward_edges), _) = s in
		match step with
		| KI.Event (Causal.RULE (rule), trace_inst) -> (
			(* Here we have found that this trace contains instantiations of the 
			 * story's rule. *)
			if IntMap.mem rule wq then (
				(* Require the story's and trace's instantiation of this rule
				 * to be identical for weak compression story matching. *)
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
					let might_add = (match IntMap.mem story_event_id forward_edges with
					| true -> IntMap.find story_event_id forward_edges 
					| false -> []) in
					(* Only add if all predecessors have been handled *)
					let all_pred_handled ((story_event_id, _) : StoryEvent.t) = (
						let pred_handled prev_handled (pred_id, _) = 
							(prev_handled && (IntMap.mem pred_id result_map))
						in
						(* All events encountered in alg have backward edges *)
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
		| _ -> (wq, result_map, is_done)

(* Create test story, initialize work queue, and begin stepping through the trace
 * starting from the first event, running the step weak algorithm function.
*) 
let check_weak_story_embeds env steps = 
	let s_option = (create_toy_story env steps) in
	match s_option with
	| Some s -> (
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
	)
	| None -> (printf "%s" "could not load test story")  

(******************************************************************************
* Strong compression algorithm
* This strong compression matching algorithm matches a particular type of 
* abstract stories to the trace it might represent. In particular, a strong 
* compression matching is valid if there is some mapping from the story's 
* agents in its instantiations to the trace's agents such that the 
* instantiations are valid. 
* This matching algorithm is a nondeterministic backwards version of the
* matching algorithm above. When a story's event can potentially be mapped
* to a trace's event, a version of the current state (wq, result_map, is_done)
* is created to represent this mapping, and another version is maintained that
* does not make this mapping.
* When a mapping is made, mappings between agents from the story and agents 
* from the trace that were made in previous steps must be maintained. To 
* achieve this, we maintain an additional data structure capturing the
* current agent identifier concretization, and make sure each step of the
* algorithm preserves that.
* 
* Known issues: 
* Right now the mapping between agent identifiers in a story's event and
* trace's event is constructed simply by taking the set of agents in a particular
* story event, and the set of agents in a particular trace event, and
* choosing a matching between them that preserves the current concretization and
* rule types. However, the assignment of agents to their concretizations will need 
* to be better:
* 1. More than just checking whether a mapping btwn agents exists, you need to
* check that the appropriate tests are applied to the appropriate agents.
* 2. Need to account for this case: multiple agents of type A in a rule, such 
* that a single story event could yield multiple potential new matches in an
* exponential way. _All possible_ valid mappings. 
*)
let get_test_mapping mapping test =
	match test with 
  | Instantiation.Is_Here (agent_id, agent_name) ->
  	IntMap.add agent_name agent_id mapping
  | Instantiation.Has_Internal (((agent_id, agent_name), _), _) ->
  	IntMap.add agent_name agent_id mapping
  | Instantiation.Is_Free ((agent_id, agent_name), _) ->
  	IntMap.add agent_name agent_id mapping
  | Instantiation.Is_Bound ((agent_id, agent_name), _) ->
  	IntMap.add agent_name agent_id mapping
  | Instantiation.Has_Binding_type (((agent_id, agent_name), _), _) ->
  	IntMap.add agent_name agent_id mapping
  | Instantiation.Is_Bound_to (((id_1, name_1), _), ((id_2, name_2), _)) -> (
  	let mapping = IntMap.add name_1 id_1 mapping in
  	IntMap.add name_2 id_2 mapping
  )

let get_action_mapping mapping action = 
	match action with
  | Instantiation.Create ((agent_id, agent_name), _) ->
   	IntMap.add agent_name agent_id mapping
  | Instantiation.Mod_internal (((agent_id, agent_name), _), _) ->
  	IntMap.add agent_name agent_id mapping
  | Instantiation.Bind (((id_1, name_1), _), ((id_2, name_2), _)) -> (
  	let mapping = IntMap.add name_1 id_1 mapping in
  	IntMap.add name_2 id_2 mapping
  )
  | Instantiation.Bind_to (((id_1, name_1), _), ((id_2, name_2), _)) -> (
  	let mapping = IntMap.add name_1 id_1 mapping in
  	IntMap.add name_2 id_2 mapping
  )
  | Instantiation.Free ((agent_id, agent_name), _) ->
  	IntMap.add agent_name agent_id mapping
  | Instantiation.Remove (agent_id, agent_name) ->
  	IntMap.add agent_name agent_id mapping

let get_agent_name_id_map (tests, (actions, _, _)) =
	let agent_name_id_map = 
		List.fold_left get_test_mapping IntMap.empty tests in
	List.fold_left get_action_mapping agent_name_id_map actions 

let find_mapping_extension mapping s_mapping t_mapping = 
	let rec extension_mapping_helper mapping s_mapping t_mapping cur_extension = 
		if IntMap.is_empty s_mapping then cur_extension
		else match cur_extension with
		| Some cur -> (
			let (m_agent_name, m_agent_id) = IntMap.choose s_mapping in
			let s_mapping = IntMap.remove m_agent_name s_mapping in
			let t_id_real = IntMap.find m_agent_name t_mapping in 
			if IntPairMap.mem (m_agent_name, m_agent_id) cur then (
				(* This agent has already been mapped to trace event *)
				let t_id = IntPairMap.find (m_agent_name, m_agent_id) cur in
				if (t_id <> t_id_real) then 
					extension_mapping_helper mapping s_mapping t_mapping None 
				else 
					extension_mapping_helper mapping s_mapping t_mapping cur_extension
			)
			else ( 
				(* This agent has not been mapped to trace event yet *)
				let cur = 
					IntPairMap.add (m_agent_name, m_agent_id) t_id_real cur
				in 
				extension_mapping_helper mapping s_mapping t_mapping (Some cur)
			)
		)
		| None -> None
	in
	extension_mapping_helper mapping s_mapping t_mapping (Some IntPairMap.empty)

(* Returns a list of (match_loc, match_event, mappings_to_add) plus an updated count
* append to the current list of the matchings *)
let find_abstract mapping trace_inst (matches_so_far, count) cur_abstract = 
	let count = count + 1 in
	let (_, (_, story_inst)) = cur_abstract in
	let t_agent_name_to_id = get_agent_name_id_map trace_inst in
	let s_agent_name_to_id = get_agent_name_id_map story_inst in
	let option_mapping_to_add =
	 	find_mapping_extension mapping s_agent_name_to_id t_agent_name_to_id in
	match option_mapping_to_add with
	| Some mapping_to_add -> 
		(matches_so_far @ [(count, cur_abstract, mapping_to_add)], count)
	| None -> (matches_so_far, count)


(* Returns list of (match_loc, match_event, mappings_to_add)
 * mapping is a IntPairMap
 * Mappings_to_add is a list of (agent_name, story_id, trace_id).
 *)
let find_rule_application mapping trace_inst potential_abstract =
	let (matchings, _) = 
		List.fold_left (find_abstract mapping trace_inst) ([], 0) potential_abstract
	in 
	if ((List.length matchings) <> 0) then Some matchings
	else None

let update_states_list s step_id rule (state_list, all_done) match_info = 
	if (all_done) then (state_list, all_done) 
	else (
		let ((forward_edges, backward_edges), _) = s in
		let (match_loc, match_event, mappings_to_add) = match_info in
		let (wq, result_map, mapping, is_done) = List.hd state_list in
		let (story_event_id, (rule_id, story_inst)) = match_event in
		(* Update result set with new mapping *)
		let new_result_map = IntMap.add story_event_id step_id result_map in
		(* Remove matched story instance from wq *)
		let new_wq = map_rem_from_list_by_id wq rule match_loc in
		(* Add new mappings *)
		let add_new_mappings (agent_name, story_id) trace_id cur_mapping =
			IntPairMap.add (agent_name, story_id) trace_id cur_mapping
		in 
		let new_mapping = 
			IntPairMap.fold add_new_mappings mappings_to_add mapping
		in
		(* Add new elements from story to wq *)
		let might_add = (match IntMap.mem story_event_id backward_edges with
		| true -> IntMap.find story_event_id backward_edges 
		| false -> []) in
		(* Only add if all predecessors have been handled *)
		let all_succ_handled ((story_event_id, _) : StoryEvent.t) = (
			let succ_handled next_handled (succ_id, _) = 
				(next_handled && (IntMap.mem succ_id result_map))
			in
			(* all events encountered in alg have backward edges *)
			List.fold_left succ_handled true (IntMap.find story_event_id forward_edges)
		) in
		let to_add = List.filter all_succ_handled might_add in
		let new_wq = add_story_events_to_map new_wq to_add in
		let is_done = IntMap.is_empty new_wq in
		(state_list @ [(new_wq, new_result_map, new_mapping, is_done)], is_done)
	)

let step_state_strong_algorithm s mark_step (states_list, all_is_done) (state) = 
	if all_is_done then (states_list, all_is_done)
	else 
		let (step_id, step) = mark_step in
		match step with
		| KI.Event (Causal.RULE (rule), trace_inst) -> (
			let (wq, _, mapping, _) = state in
			if IntMap.mem rule wq then (
				(* See if any rule application is applicable given current mapping. Returns
				* location of match in the list, updated mapping *)
				let potential_abstract = IntMap.find rule wq in
				let match_option = 
					find_rule_application mapping trace_inst potential_abstract in
				match match_option with
				| Some match_infos -> (
					List.fold_left (update_states_list s step_id rule) ([state], false) match_infos
				)
				| None -> (states_list @ [state], all_is_done)  (* No matching instantiation *)
			)
			else (states_list @ [state], all_is_done)  (* No matching rule *)
		)
		| _ -> (states_list @ [state], all_is_done)

(*
 * Step through all possible states (all possible story event to trace event
 * mappings), at each state attempting to add an additional story event to trace event
 * mapping based on the current trace step mark_step, and returning the 
 * new set of possible states of the algorithm.  
 *)
let step_states_strong_algorithm s (states_list, all_is_done) mark_step = 
	if all_is_done then (states_list, all_is_done)
	else 
		List.fold_left (step_state_strong_algorithm s mark_step) ([], false) states_list

(* 
 * The entry point for the strongly compressed story matching algorithm. 
 * Nondeterministically tries to assign events of the story to the trace, walking
 * through the trace and story backwards from the event of interest.
 *)
let check_strong_story_embeds env steps = 
	let s_option = (create_toy_story env steps) in
	match s_option with
	| Some s -> (
		let ((_, _), last_events) = s in
		let wq = IntMap.empty in (* wq is map from rule id to story_events *)
		let result_map = IntMap.empty in (* result_map maps story_event ids to trace id *)
		let mapping = IntPairMap.empty in (* mapping captures the current concretization of agents *)
		let wq = add_story_events_to_map wq last_events in (* Initialize wq *)
		let param = [(wq, result_map, mapping, false)] in
		let (_,is_done) = 
			List.fold_left (step_states_strong_algorithm s) 
				(param, false) (mark_steps_with_id (List.rev steps))
		in
		if is_done then (printf "%s " "matches")
		else (printf "%s " "doesn't match") 
	)
	| None -> (printf "%s" "could not load test story")  

(***********************************************************************
* Printing traces for debugging
*)
let print_trace env steps = 
  Format.eprintf "@[<v>%a@]" (Pp.list Pp.space KI.print_refined_step) steps

let print_rule env f step = 
	match step with 
	| KI.Event (Causal.RULE (rule), _) ->
		Environment.print_rule ~env:env Format.err_formatter rule
	| _ -> ()

let print_rules env steps =
	Format.eprintf "@[<v>%a@]" (Pp.list Pp.space (print_rule env)) steps
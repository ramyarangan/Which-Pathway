 
module KI = Utilities.S.PH.B.PB.CI.Po.K

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

(* story data structure - hash map of node to list of its neighbors. adjacency list
* get trace instantiations 
* get sample story, build sample trace 
* *)
(** Algebraic and boolean expression manager *)

(** {6 Printers} *)

val print_ast_mix : Format.formatter -> Ast.mixture -> unit
val print_ast_alg : Format.formatter -> Ast.mixture Ast.ast_alg_expr -> unit

val print_bool :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a Ast.bool_expr -> unit
val print_ast_bool :
  Format.formatter -> Ast.mixture Ast.ast_alg_expr Ast.bool_expr -> unit

(** {6 Utilities } *)
val ast_alg_has_mix : 'a Ast.ast_alg_expr Term.with_pos -> bool

(** {6 Compilers } *)

(** [compile_alg variable_map token_map (fresh_mix_id, mix_list) alg_pos] *)
val compile_alg :
  ?origin:Term.rev_dep -> int Mods.StringMap.t -> int Mods.StringMap.t ->
  ?max_allowed_var:int ->
  (string list * (string * string) list) Export_to_KaSim.String2Map.t ->
  Connected_component.Env.t ->
  Ast.mixture Ast.ast_alg_expr Term.with_pos ->
  Connected_component.Env.t * Alg_expr.t Term.with_pos
val compile_pure_alg :
  int Mods.StringMap.t -> int Mods.StringMap.t ->
  Ast.mixture Ast.ast_alg_expr Term.with_pos -> Alg_expr.t Term.with_pos
val compile_bool :
  int Mods.StringMap.t -> int Mods.StringMap.t ->
  (string list * (string * string) list) Export_to_KaSim.String2Map.t ->
  Connected_component.Env.t ->
  Ast.mixture Ast.ast_alg_expr Ast.bool_expr Term.with_pos ->
  Connected_component.Env.t * Alg_expr.t Ast.bool_expr Term.with_pos

val stops_of_bool_expr :
  (Term.DepSet.t * Term.DepSet.t * Term.DepSet.t array) ->
  Alg_expr.t Ast.bool_expr -> Nbr.t list

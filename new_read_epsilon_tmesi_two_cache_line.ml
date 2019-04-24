(* TMESI automaton with only one variable per cache line *)

open Printf

type status =  Active | Aborted | Committed |Invalid | Non_exist
type var = V1 | V2
type thread = T1 | T2
type flag = int
type in_com = int (* 0 if the transaction is not in the procedure of commit and >0 otherwise *)
type eps = int (* 1 if the transition before this state is com_one which prints out "rd, t1" etc, 2 if it is com_two, 0 otherwise *)
type var_info = thread * var
type rw_cfl = (var_info option) * (var_info option) (* Read-write conflict. Here the cache line is not included, since there is only one variable on per cache line in this automaton *)
type wr_cfl = (var_info option) * (var_info option) (*write-read conflict*)
type ww_cfl = (var_info option) * (var_info option) (*write-write conflict*)
type readSet = var option * var option
type writeSet = var option * var option
type cls = TMI | TI | M | E | S | I | N_E (* Non-exist state *)
type cls_set = cls * cls

type state = status * flag * in_com * eps * readSet * writeSet * rw_cfl * wr_cfl * ww_cfl * cls_set
type statePair = state * state

let status_to_string = function | Active -> "active" | Aborted -> "aborted" | Committed -> "committed" |Invalid -> "invalid" | Non_exist -> "non_exist"
let var_to_string = function | None -> "n" | Some V1 -> "v1" | Some V2 -> "v2"
let var_info_to_string = function | None -> "n" | Some (T1, V1) -> "(t1, v1)" | Some (T1, V2) -> "(t1, v2)" | Some (T2, V1) -> "(t2, v1)" | Some (T2, V2) -> "(t2, v2)"
let flag_to_string = string_of_int
let in_com_to_string = string_of_int
let eps_to_string = string_of_int
let print_wrSet (v1, v2) = "(" ^ var_to_string v1 ^ ", " ^ var_to_string v2 ^ ")"
let cfl_to_string (vi1, vi2) = "(" ^ var_info_to_string vi1 ^ ", " ^ var_info_to_string vi2 ^ ")"
let print_rw_cfl cfl = " rw" ^ cfl_to_string cfl (* ^ ")" *)
let print_wr_cfl cfl = " wr" ^ cfl_to_string cfl (* ^ ")"  *)
let print_ww_cfl cfl = " ww" ^ cfl_to_string cfl (* ^ ")"  *)
let cls_to_string = function | TMI -> "tmi" | TI -> "ti" | M -> "m" | E -> "e" | S -> "s" | I -> "i" | N_E -> "n-e"
let print_cls_set cls_set = "(" ^ cls_to_string (fst(cls_set)) ^ ", " ^ cls_to_string (snd(cls_set)) ^ ") "

let print_state ((sta, flg, in_com, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls): state) = begin
  let sta_s = status_to_string sta in
  let flag_s = flag_to_string flg in
  let in_com_s = in_com_to_string in_com in
  let eps_s = eps_to_string eps in
  let rs_s = print_wrSet rs in
  let ws_s = print_wrSet ws in
  let rw_cfl_s = print_rw_cfl rw_cfl in
  let wr_cfl_s = print_wr_cfl wr_cfl in
  let ww_cfl_s = print_ww_cfl ww_cfl in
  let cls_s= print_cls_set cls in
  sta_s^flag_s^in_com_s^eps_s^rs_s^ws_s^rw_cfl_s^wr_cfl_s^ww_cfl_s^cls_s
end

let print_state_pair state1 state2 = begin
  let s1 = print_state state1 in
  let s2 = print_state state2 in
  s1^s2
end

let var_in_set v wr_set = begin
  match wr_set with
  | Some v1, _ when v = v1 -> true
  | _, Some v2 when v = v2 -> true
  | _, _ -> false
end

let add_var (v: var) wr_set = begin
  match var_in_set v wr_set with
  | true -> wr_set
  | _ -> begin
      match v with
      | V1 -> (Some v, snd(wr_set))
      |	_  -> (fst(wr_set), Some v)
  end
end

let var_in_cfl (vi: var_info) cfl = begin
  match cfl with
  | Some vi1, _ when vi = vi1 -> true
  | _, Some vi2 when vi = vi2 -> true
  | _, _ -> false
end

let add_ci (ci: var_info) cfl = begin
  match var_in_cfl ci cfl with
  | true -> cfl
  | _ -> begin
      match ci with
      |	(_, V1) -> (Some ci, snd(cfl))
      |	(_, _) -> (fst(cfl), Some ci)
  end
end

let if_inter wr_set1 wr_set2 = begin
  match wr_set1, wr_set2 with
  | (Some (_, V1), _), (Some (_, V1), _) -> true
  | (_, Some (_, V2)), (_, Some (_, V2)) -> true
  | (_, _), (_, _) -> false
end

let aborted_cls cls1 cls2 = begin
  match cls1, cls2 with
  | TMI, TMI -> (I, cls2)
  | TMI, TI -> (I, cls2)
  | TMI, I -> (I, cls2)
  | TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
  | TI, TMI -> (I, cls2)
  | TI, S -> (I, cls2)
  | TI, I -> (I, cls2)
  | TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
  | I, _ -> (cls1, cls2) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx aborts, the I cache line state doesn't change *)
  | _, I -> (cls1, cls2) (* M/E/S, I *)
  | S, S -> (cls1, cls2)
  | S, TI -> (cls1, cls2)
  | _, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
end

let naborted_cls cls1 cls2 = begin
  match cls1, cls2 with
  | TMI, TMI -> (I, cls2)
  | TMI, I -> (I, cls2)
  | _, _ -> (cls1, cls2)
end

let get_status state = begin
  match state with
  | (sta, _, _, _, _, _, _, _, _, _) -> sta
end

let check_status state_pair i = begin
  match i with
  | 1 -> get_status (fst(state_pair))
  | _ -> get_status (snd(state_pair))
end

module StateSet = Set.Make(struct type t = (state * state) let compare = Pervasives.compare end)
module Forward = Hashtbl.Make(struct
  type t = (state * state) * string
  let hash = Hashtbl.hash
  let equal = (=)
end)

module States = Hashtbl.Make(struct
  type t = (state * state)
  let hash = Hashtbl.hash
  let equal = (=)
end)

module Eps_trans = Hashtbl.Make(struct
  type t = (state * state) * string
  let hash = Hashtbl.hash
  let equal = (=)
end)

let forward : (state * state) Forward.t = Forward.create 0
let states : int States.t = States.create 0
let eps_trans : (state * state) Eps_trans.t = Eps_trans.create 0

let state_no = ref 0

let rec polish_state acc state_pair = begin
  let len = String.length state_pair in
  match state_pair with
  | "" -> acc
  | _ -> begin
      let s = String.sub state_pair 0 1 in (*** TODO: try to use s.[n] to get the character if the program is not fast enough ***)
      match s with
      | "(" -> begin let head = acc ^ "L" in let tail = String.sub state_pair 1 (len -1) in polish_state head tail end
      | ")" -> begin let head = acc ^ "R" in let tail = String.sub state_pair 1 (len -1) in polish_state head tail end
      | "," -> begin let tail = String.sub state_pair 1 (len -1) in polish_state acc tail end
      | " " -> begin let tail = String.sub state_pair 1 (len -1) in polish_state acc tail end
      |	_ -> begin let head = acc ^ s in let tail = String.sub state_pair 1 (len -1) in polish_state head tail end
  end
end

let rec polish_transition acc transition = begin
  let len = String.length transition in
  match transition with
  | "" -> acc
  | _ -> begin
      let s = String.sub transition 0 1 in (*** TODO: try to use s.[n] to get the character if the program is not fast enough ***)
      match s with
      | "," -> begin let tail = String.sub transition 1 (len -1) in polish_transition acc tail end
      | " " -> begin let tail = String.sub transition 1 (len -1) in polish_transition acc tail end
      |	_ -> begin let head = acc ^ s in let tail = String.sub transition 1 (len -1) in polish_transition head tail end
  end
end

let init_state_pair = ((Committed, 0, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Committed, 0, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)))
let non_exist = ((Non_exist, 0, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)))

let str_init = print_state_pair (fst(init_state_pair)) (snd(init_state_pair))
let p_init = polish_state "" str_init;;
let t_file = "TMESI_two_cache_line_Transitions.ml"
let f_file = "TMESI_two_cache_line_Final_states.ml"
let s_file = "TMESI_two_cache_line_States.ml"
let o_t = open_out t_file;;
let o_f = open_out f_file;;
let o_s = open_out s_file;;
fprintf o_t "Transitions\ni -> %s\n" p_init;;
fprintf o_f "Final States\n";;
fprintf o_s "States\n";;

let print_to_files state1 state2 post str = begin
  let state_str = print_state_pair state1 state2 in
  let p_state_str = polish_state "" state_str in
  let post_str = print_state_pair (fst(post)) (snd(post)) in
  let p_post_str = polish_state "" post_str in
  let t_str = str^"("^p_state_str^")"^" -> "^p_post_str in
  fprintf o_t "%s\n" t_str
end

let print_states_to_file hkey = begin
  if (check_status hkey 1) = Non_exist then ()
  else begin
  try
    ignore(States.find states hkey)
  with Not_found -> begin
    state_no := (!state_no) + 1;
    States.add states hkey (!state_no);
    let hkey_str = print_state_pair (fst(hkey)) (snd(hkey)) in
    let p_hkey_str = polish_state "" hkey_str in
    (* printf "State %d printed to the file TMESI_States.ml:\n%s\n" (!state_no) p_hkey_str; *)
    fprintf o_s "%s\n" p_hkey_str
  end
end
end
;;

let tread_t1_v1 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls11, cls21 with
      | I, I -> (E, cls21)
      |	I, TMI -> (TI, cls21)
      |	I, TI -> (S, cls21)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	TMI, TMI -> (cls11, cls21)
      |	TMI, TI -> (cls11, cls21)
      |	TMI, I -> (cls11, cls21)
      |	TMI, _ -> (N_E, N_E) (* TMI and M/E/S cannot exist at the same time*)
      |	TI, M -> (N_E, N_E)
      |	TI, E -> (N_E, N_E)
      |	TI, TI -> (N_E, N_E)
      |	TI, _ -> (cls11, cls21) (* TI, TMI/S/I *)
      |	_, I -> (cls11, cls21) (* M/E/S, I *)
      |	S, TI -> (cls11, cls21)
      |	S, S -> (cls11, cls21)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let rs = add_var v rs1 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws2 with
	| true -> ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    ((sta, flg1, in_com1, eps1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls1_f, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls2_f, cls22)))
    end
  end
end

let tread_t1_v2 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls12, cls22 with
      | I, I -> (E, cls22)
      |	I, TMI -> (TI, cls22)
      |	I, TI -> (S, cls22)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	TMI, TMI -> (cls12, cls22)
      |	TMI, TI -> (cls12, cls22)
      |	TMI, I -> (cls12, cls22)
      |	TMI, _ -> (N_E, N_E) (* TMI and M/E/S cannot exist at the same time*)
      |	TI, M -> (N_E, N_E)
      |	TI, E -> (N_E, N_E)
      |	TI, TI -> (N_E, N_E)
      |	TI, _ -> (cls12, cls22) (* TI, TMI/S/I *)
      |	_, I -> (cls12, cls22) (* M/E/S, I *)
      |	S, TI -> (cls12, cls22)
      |	S, S -> (cls12, cls22)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let rs = add_var v rs1 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws2 with
	| true -> ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    ((sta, flg1, in_com1, eps1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls11, cls1_f)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls21, cls2_f)))
    end
  end
end

let tread_t2_v1 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls21, cls11 with
      | I, I -> (E, cls11)
      |	I, TMI -> (TI, cls11)
      |	I, TI -> (S, cls11)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	TMI, TMI -> (cls21, cls11)
      |	TMI, TI -> (cls21, cls11)
      |	TMI, I -> (cls21, cls11)
      |	TMI, _ -> (N_E, N_E) (* TMI and M/E/S cannot exist at the same time*)
      |	TI, M -> (N_E, N_E)
      |	TI, E -> (N_E, N_E)
      |	TI, TI -> (N_E, N_E)
      |	TI, _ -> (cls21, cls11) (* TI, TMI/S/I *)
      |	_, I -> (cls21, cls11) (* M/E/S, I *)
      |	S, TI -> (cls21, cls11)
      |	S, S -> (cls21, cls11)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
   in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let rs = add_var v rs2 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws1 with
	| true -> ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls1_f, cls12)), (sta, flg2, in_com2, eps2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls2_f, cls22)))
    end
  end
end

let tread_t2_v2 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls22, cls12 with
      | I, I -> (E, cls12)
      |	I, TMI -> (TI, cls12)
      |	I, TI -> (S, cls12)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	TMI, TMI -> (cls22, cls12)
      |	TMI, TI -> (cls22, cls12)
      |	TMI, I -> (cls22, cls12)
      |	TMI, _ -> (N_E, N_E) (* TMI and M/E/S cannot exist at the same time*)
      |	TI, M -> (N_E, N_E)
      |	TI, E -> (N_E, N_E)
      |	TI, TI -> (N_E, N_E)
      |	TI, _ -> (cls22, cls12) (* TI, TMI/S/I *)
      |	_, I -> (cls22, cls12) (* M/E/S, I *)
      |	S, TI -> (cls22, cls12)
      |	S, S -> (cls22, cls12)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
   in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let rs = add_var v rs2 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws1 with
	| true -> ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls11, cls1_f)), (sta, flg2, in_com2, eps2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls21, cls2_f)))
    end
  end
end

let twrite_t1_v1 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls11, cls21 with
      | _, I -> (TMI, cls21) (* TMI/TI/M/E/S/I, I *)
      |	I, TMI -> (TMI, cls21)
      |	TI, TMI -> (TMI, cls21)
      |	TMI, TMI -> (cls11, cls21)
      |	_, TMI -> (N_E, N_E) (* M/E/S, TMI *)
      |	S, TI -> (TMI, cls21)
      |	I, TI -> (TMI, cls21)
      |	TMI, TI -> (cls11, cls21)
      |	_, TI -> (N_E, N_E) (* M/E/TI, TI *)
      |	I, _ -> (TMI, I) (* I, M/E/S *)
      |	S, S -> (TMI, I)
      |	TI, S -> (TMI, I)
      |	_, _ -> (N_E, N_E) (* TMI/M/E/S, M/E and TMI/TI/M/E, S *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let ws = add_var v ws1 in
      let (wr_cfl, rw_cfl) =
	match var_in_set v rs2 with
	| true -> ((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2))
	| _ -> (wr_cfl1, rw_cfl2)
      in
      let (ww_cfl1_f, ww_cfl2_f) =
	match var_in_set v ws2 with
	| true -> ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2))
	| _ -> (ww_cfl1, ww_cfl2)
      in
    ((sta, flg1, in_com1, eps1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls1_f, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls2_f, cls22)))
    end
  end
end

let twrite_t1_v2 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls12, cls22 with
      | _, I -> (TMI, cls22) (* TMI/TI/M/E/S/I, I *)
      |	I, TMI -> (TMI, cls22)
      |	TI, TMI -> (TMI, cls22)
      |	TMI, TMI -> (cls12, cls22)
      |	_, TMI -> (N_E, N_E) (* M/E/S, TMI *)
      |	S, TI -> (TMI, cls22)
      |	I, TI -> (TMI, cls22)
      |	TMI, TI -> (cls12, cls22)
      |	_, TI -> (N_E, N_E) (* M/E/TI, TI *)
      |	I, _ -> (TMI, I) (* I, M/E/S *)
      |	S, S -> (TMI, I)
      |	TI, S -> (TMI, I)
      |	_, _ -> (N_E, N_E) (* TMI/M/E/S, M/E and TMI/TI/M/E, S *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let ws = add_var v ws1 in
      let (wr_cfl, rw_cfl) =
	match var_in_set v rs2 with
	| true -> ((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2))
	| _ -> (wr_cfl1, rw_cfl2)
      in
      let (ww_cfl1_f, ww_cfl2_f) =
	match var_in_set v ws2 with
	| true -> ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2))
	| _ -> (ww_cfl1, ww_cfl2)
      in
    ((sta, flg1, in_com1, eps1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls11, cls1_f)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls21, cls2_f)))
    end
  end
end

let twrite_t2_v1 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com2 != 0) then non_exist
 else begin
    let (cls2_f, cls1_f) =
      match cls21, cls11 with
      | _, I -> (TMI, cls11) (* TMI/TI/M/E/S/I, I *)
      |	I, TMI -> (TMI, cls11)
      |	TI, TMI -> (TMI, cls11)
      |	TMI, TMI -> (cls21, cls11)
      |	_, TMI -> (N_E, N_E) (* M/E/S, TMI *)
      |	S, TI -> (TMI, cls11)
      |	I, TI -> (TMI, cls11)
      |	TMI, TI -> (cls21, cls11)
      |	_, TI -> (N_E, N_E) (* M/E/TI, TI *)
      |	I, _ -> (TMI, I) (* I, M/E/S *)
      |	S, S -> (TMI, I)
      |	TI, S -> (TMI, I)
      |	_, _ -> (N_E, N_E) (* TMI/M/E/S, M/E and TMI/TI/M/E, S *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let ws = add_var v ws2 in
      let (wr_cfl, rw_cfl) =
	match var_in_set v rs1 with
	| true -> ((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1))
	| _ -> (wr_cfl2, rw_cfl1)
      in
      let (ww_cfl1_f, ww_cfl2_f) =
	match var_in_set v ws1 with
	| true -> ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2))
	| _ -> (ww_cfl1, ww_cfl2)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls1_f, cls12)), (sta, flg2, in_com2, eps2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls2_f, cls22)))
    end
  end
end

let twrite_t2_v2 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com2 != 0) then non_exist
 else begin
    let (cls2_f, cls1_f) =
      match cls22, cls12 with
      | _, I -> (TMI, cls12) (* TMI/TI/M/E/S/I, I *)
      |	I, TMI -> (TMI, cls12)
      |	TI, TMI -> (TMI, cls12)
      |	TMI, TMI -> (cls22, cls12)
      |	_, TMI -> (N_E, N_E) (* M/E/S, TMI *)
      |	S, TI -> (TMI, cls12)
      |	I, TI -> (TMI, cls12)
      |	TMI, TI -> (cls22, cls12)
      |	_, TI -> (N_E, N_E) (* M/E/TI, TI *)
      |	I, _ -> (TMI, I) (* I, M/E/S *)
      |	S, S -> (TMI, I)
      |	TI, S -> (TMI, I)
      |	_, _ -> (N_E, N_E) (* TMI/M/E/S, M/E and TMI/TI/M/E, S *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let ws = add_var v ws2 in
      let (wr_cfl, rw_cfl) =
	match var_in_set v rs1 with
	| true -> ((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1))
	| _ -> (wr_cfl2, rw_cfl1)
      in
      let (ww_cfl1_f, ww_cfl2_f) =
	match var_in_set v ws1 with
	| true -> ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2))
	| _ -> (ww_cfl1, ww_cfl2)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls11, cls1_f)), (sta, flg2, in_com2, eps2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls21, cls2_f)))
    end
  end
end

let abort_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta1 = Committed || sta1 = Aborted) || flg1 != 0) || flg2 != 0) (* || in_com1 != 0) || in_com2 != 0) *) then non_exist
  else begin
    let (cls11_f, cls21_f) =
      match cls11, cls21 with
      | TMI, TMI -> (I, cls21)
      | TMI, TI -> (I, cls21)
      | TMI, I -> (I, cls21)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls21)
      |	TI, S -> (I, cls21)
      |	TI, I -> (I, cls21)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls11, cls21) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx aborts, the I cache line state doesn't change *)
      |	_, I -> (cls11, cls21) (* M/E/S, I *)
      |	S, S -> (cls11, cls21)
      |	S, TI -> (cls11, cls21)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    let (cls12_f, cls22_f) =
      match cls12, cls22 with
      | TMI, TMI -> (I, cls22)
      | TMI, TI -> (I, cls22)
      | TMI, I -> (I, cls22)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls22)
      |	TI, S -> (I, cls22)
      |	TI, I -> (I, cls22)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls12, cls22) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx aborts, the I cache line state doesn't change *)
      |	_, I -> (cls12, cls22) (* M/E/S, I *)
      |	S, S -> (cls12, cls22)
      |	S, TI -> (cls12, cls22)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if ((cls11_f, cls21_f) = (N_E, N_E)||(cls12_f, cls22_f) = (N_E, N_E)) then non_exist
    else begin
      let sta = Aborted in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = (None, None) in
      let wr_cfl = (None, None) in
      let ww_cfl = (None, None) in
      let in_com2_f = in_com2 + 1 in
      let output = ((sta, flg1, 0, 0, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, in_com2_f, 0, rs2, ws2, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))) in
      print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "abtt1";
      output
    end
  end
end

let abort_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta2 = Committed || sta2 = Aborted) || flg1 != 0) || flg2 != 0) (* || in_com1 != 0) || in_com2 != 0) *) then begin non_exist
    end
  else begin
    let (cls21_f, cls11_f) =
      match cls21, cls11 with
      | TMI, TMI -> (I, cls11)
      | TMI, TI -> (I, cls11)
      | TMI, I -> (I, cls11)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls11)
      |	TI, S -> (I, cls11)
      |	TI, I -> (I, cls11)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls21, cls11) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx aborts, the I cache line state doesn't change *)
      |	_, I -> (cls21, cls11) (* M/E/S, I *)
      |	S, S -> (cls21, cls11)
      |	S, TI -> (cls21, cls11)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/TI/M/E *)
    in
    let (cls22_f, cls12_f) =
      match cls22, cls12 with
      | TMI, TMI -> (I, cls12)
      | TMI, TI -> (I, cls12)
      | TMI, I -> (I, cls12)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls12)
      |	TI, S -> (I, cls12)
      |	TI, I -> (I, cls12)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls22, cls12) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx aborts, the I cache line state doesn't change *)
      |	_, I -> (cls22, cls12) (* M/E/S, I *)
      |	S, S -> (cls22, cls12)
      |	S, TI -> (cls22, cls12)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/TI/M/E *)
    in
    if ((cls11_f, cls21_f) = (N_E, N_E)||(cls12_f, cls22_f) = (N_E, N_E)) then non_exist
    else begin
      let sta = Aborted in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = (None, None) in
      let wr_cfl = (None, None) in
      let ww_cfl = (None, None) in
      let in_com1_f = in_com1 + 1 in
      let output = ((sta1, flg1, in_com1_f, 0, rs1, ws1, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta, flg2, 0, 0, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))) in
      print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "abtt2";
      (* if output = non_exist then printf "Output is non_exist.\n"; *)
      output
    end
  end
end

let commit_one_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  let eps = 1 in
  
  if ((((sta1 = Aborted || sta1 = Committed) || flg1 != 0) || flg2 != 0) || in_com1 != 0) then non_exist
  else begin
    if (in_com2 != 0) then begin
      let in_com1_f = in_com1 + 1 in
      let in_com2_f = in_com2 + 1 in
      let output = ((sta1, flg1, in_com1_f, eps, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22))) in
      Eps_trans.add eps_trans (output, "com_one, t1") ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)));
      (* let print output = begin *)
      (* match (var_in_set V1 rs1), (var_in_set V2 rs1), (var_in_set V1 ws1), (var_in_set V2 ws1) with *)
      (* |	true, _, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "rdt1v1" *)
      (* |	_, true, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "rdt1v2" *)
      (* |	_, _, true, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "wrt1v1" *)
      (* |	_, _, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "wrt1v2" *)
      (* end in *)
      (* print output; *)
      output
    end
    
    else begin
      let if_abort = begin
      	match wr_cfl1, rw_cfl2, ww_cfl1, ww_cfl2 with
        | (Some (T2, _), _), (Some (T1, _), _), _, _ -> true (* the other tx should be aborted only when the cfl in both threads are unempty, because sometimes the neighbour can be aborted or committed *)
        | (_, Some (T2, _)), (_, Some (T1, _)), _, _ -> true
      	| _, _, (Some (T2, _), _), (Some (T1, _), _) -> true
      	| _, _, (_, Some (T2, _)), (_, Some (T1, _)) -> true
      	| _, _, _, _ -> false
      end in
      
      let in_com1_f = in_com1 + 1 in
      (* eps1 and eps2 do not change in output_abt because it is not an epsilon transition. *) 
      (* if eps1/2 !=0 then it means there is an eps transition before this commit_one function, otherwise it is just shown as a normal transition 0 -> (abt) 0*)
      let output_abt = ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22))) in
      let output_eps = ((sta1, flg1, in_com1_f, eps, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22))) in
      
      match if_abort with
      |	true ->  begin
	  print_states_to_file output_abt;
	  abort_t2 (fst(output_abt)) (snd(output_abt))
      end
      |	_ -> begin
	  Eps_trans.add eps_trans (output_eps, "com_one, t1") ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)));
	  (* let print output_eps = begin *)
	  (*       match (var_in_set V1 rs1), (var_in_set V2 rs1), (var_in_set V1 ws1), (var_in_set V2 ws1) with *)
	  (* 	| true, _, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_eps "rdt1v1" *)
	  (* 	| _, true, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_eps "rdt1v2" *)
	  (* 	| _, _, true, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_eps "wrt1v1" *)
	  (* 	| _, _, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_eps "wrt1v2" *)
          (* end in *)
	  (* print output_eps; *)
	  output_eps
      end
    end
  end
end

let commit_one_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  let eps = 1 in
  
  if ((((sta2 = Aborted || sta2 = Committed) || flg1 != 0) || flg2 != 0) || in_com2 != 0) then non_exist
  else begin
    if (in_com1 != 0) then begin
      let in_com1_f = in_com1 + 1 in
      let in_com2_f = in_com2 + 1 in
      let output = ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2_f, eps, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22))) in
      Eps_trans.add eps_trans (output, "com_one, t2") ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)));
      (* let print output = begin *)
      (* match (var_in_set V1 rs2), (var_in_set V2 rs2), (var_in_set V1 ws2), (var_in_set V2 ws2) with *)
      (* |	true, _, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "rdt2v1" *)
      (* |	_, true, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "rdt2v2" *)
      (* |	_, _, true, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "wrt2v1" *)
      (* |	_, _, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "wrt2v2" *)
      (* end in *)
      (* print output; *)
      output
    end
  
    else begin
      let if_abort = begin
      	match wr_cfl2, rw_cfl1, ww_cfl2, ww_cfl1 with
        | (Some (T1, _), _), (Some (T2, _), _), _, _ -> true
        | (_, Some (T1, _)), (_, Some (T2, _)), _, _ -> true
      	| _, _, (Some (T1, _), _), (Some (T2, _), _) -> true
      	| _, _, (_, Some (T1, _)), (_, Some (T2, _)) -> true
      	| _, _, _, _ -> false
      end in
      
      let in_com2_f = in_com2 + 1 in
      let output_abt = ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22))) in
      let output_eps = ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2_f, eps, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22))) in
     
      match if_abort with
      |	true -> begin
	  print_states_to_file output_abt;
	  abort_t1 (fst(output_abt)) (snd(output_abt))
      end
      |	_ -> begin
	  Eps_trans.add eps_trans (output_eps, "com_one, t2") ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)));
          
          (* let pre_test = *)
	  (*   try *)
	  (*     Eps_trans.find eps_trans (output_eps, "com_one, t2") *)
	  (*   with Not_found -> non_exist *)
	  (* in *)
	  (* printf "The pre t2 state of \n%s is: \n%s \n" (print_state_pair (fst(output_eps)) (snd(output_eps))) (print_state_pair (fst(pre_test)) (snd(pre_test))); *)
	  
          (* let print output_eps = begin *)
	  (*       match (var_in_set V1 rs2), (var_in_set V2 rs2), (var_in_set V1 ws2), (var_in_set V2 ws2) with *)
	  (* 	| true, _, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_eps "rdt2v1" *)
	  (* 	| _, true, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_eps "rdt2v2" *)
	  (* 	| _, _, true, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_eps "wrt2v1" *)
	  (* 	| _, _, _, _ -> print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_eps "wrt2v2" *)
          (* end in *)
	  (* print output_eps; *)
	  output_eps
      end
    end
  end
end

let commit_two_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  let eps = 0 in
  
  if (((((sta1 = Aborted || sta1 = Committed) || flg1 != 0) || flg2 != 0) || in_com1 = 0) || in_com1 < in_com2) then non_exist
  else begin
    let (cls11_f, cls21_f) =
      match cls11, cls21 with
      | TMI, TMI -> (M, I)
      | TMI, TI -> (M, I)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls21)
      |	TI, S -> (I, cls21)
      |	TI, I -> (I, cls21)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls11, cls21) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls11, cls21) (* M/E/S, I *)
      |	S, S -> (cls11, cls21)
      |	S, TI -> (cls11, cls21)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    let (cls12_f, cls22_f) =
      match cls12, cls22 with
      | TMI, TMI -> (M, I)
      | TMI, TI -> (M, I)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls22)
      |	TI, S -> (I, cls22)
      |	TI, I -> (I, cls22)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls12, cls22) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls12, cls22) (* M/E/S, I *)
      |	S, S -> (cls12, cls22)
      |	S, TI -> (cls12, cls22)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if ((cls11_f, cls21_f) = (N_E, N_E)||(cls12_f, cls22_f) = (N_E, N_E)) then non_exist
    
    else begin
      let if_abort = begin
      	match wr_cfl1, rw_cfl2, ww_cfl1, ww_cfl2 with
        | (Some (T2, _), _), (Some (T1, _), _), _, _ -> true (* the other tx should be aborted only when the cfl in both threads are unempty, because sometimes the neighbour can be aborted or committed *)
        | (_, Some (T2, _)), (_, Some (T1, _)), _, _ -> true
      	| _, _, (Some (T2, _), _), (Some (T1, _), _) -> true
      	| _, _, (_, Some (T2, _)), (_, Some (T1, _)) -> true
      	| _, _, _, _ -> false
      end in
      
      let empty_wr = begin
	match rw_cfl1 with
	| (Some (T2, _), _) -> true
	| (_, Some (T2, _)) -> true
	| _ -> false
      end in
      
      let in_com1_f = 0 in
      let in_com2_f = 0 in
      let output = ((sta1, flg1, in_com1_f, eps, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22))) in
      
      if (if_abort = true) then begin
	(* let print output = begin *)
	(*   match (var_in_set V1 rs1), (var_in_set V2 rs1), (var_in_set V1 ws1), (var_in_set V2 ws1) with *)
	(*     | true, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "rdt1v1"; *)
	(* 	print_states_to_file output *)
	(*     | _, true, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "rdt1v2"; *)
	(* 	print_states_to_file output *)
	(*     | _, _, true, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "wrt1v1"; *)
	(* 	print_states_to_file output *)
	(*     | _, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "wrt1v2"; *)
	(* 	print_states_to_file output *)
	(* end in *)
	(* print output;  *)
	let output_abt = commit_one_t1 (fst(output)) (snd(output)) in
	
        (* if (get_status (snd(output_abt))) != Aborted  *)
	(* then printf "The output_abt by invoking commit_one_t1 for %s\n is\n %s\n" (print_state_pair (fst(output)) (snd(output))) ((print_state_pair (fst(output_abt)) (snd(output_abt)))); *)
	
        (* if eps2 != 0 then the output of the commit_two function should go through the get_pre function later in after_commit_two *)
	if eps2 != 0 then output_abt else begin
	  print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_abt "abtt2";
	  output_abt
	end
      end
      
      else begin
	let sta = Committed in
	let rs = (None, None) in
	let ws = (None, None) in
	let rw_cfl = (None, None) in
	let wr_cfl = (None, None) in
	let ww_cfl = (None, None) in
	let output_com = begin
	  match empty_wr with
	  | true -> ((sta, flg1, in_com1_f, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, (None, None), ww_cfl2, (cls21_f, cls22_f)))
	  | false -> ((sta, flg1, in_com1_f, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21_f, cls22_f))) end in
	(* if eps2 != 0 then the output of the commit_two function should go through the get_pre function later in after_commit_two *)
	if eps2 != 0 then output_com
	else begin
	  print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_com "comt1";
	  output_com
	end
      end
    end
  end
end

let commit_two_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  let eps = 0 in
  
  if (((((sta2 = Aborted || sta2 = Committed) || flg1 != 0) || flg2 != 0) || in_com2 = 0) || in_com2 < in_com1) then non_exist
  else begin
    let (cls21_f, cls11_f) =
      match cls21, cls11 with
      | TMI, TMI -> (M, I)
      | TMI, TI -> (M, I)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls11)
      |	TI, S -> (I, cls11)
      |	TI, I -> (I, cls11)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls21, cls11) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls21, cls11) (* M/E/S, I *)
      |	S, S -> (cls21, cls11)
      |	S, TI -> (cls21, cls11)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/TI/M/E *)
    in
    let (cls22_f, cls12_f) =
      match cls22, cls12 with
      | TMI, TMI -> (M, I)
      | TMI, TI -> (M, I)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls12)
      |	TI, S -> (I, cls12)
      |	TI, I -> (I, cls12)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls22, cls12) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls22, cls12) (* M/E/S, I *)
      |	S, S -> (cls22, cls12)
      |	S, TI -> (cls22, cls12)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/TI/M/E *)
    in
    if ((cls11_f, cls21_f) = (N_E, N_E)||(cls12_f, cls22_f) = (N_E, N_E)) then non_exist
    else begin
      let if_abort = begin
      	match wr_cfl2, rw_cfl1, ww_cfl2, ww_cfl1 with
        | (Some (T1, _), _), (Some (T2, _), _), _, _ -> true
        | (_, Some (T1, _)), (_, Some (T2, _)), _, _ -> true
      	| _, _, (Some (T1, _), _), (Some (T2, _), _) -> true
      	| _, _, (_, Some (T1, _)), (_, Some (T2, _)) -> true
      	| _, _, _, _ -> false
      end in
      
      let empty_wr = begin
	match rw_cfl2 with
	| (Some (T1, _), _) -> true
	| (_, Some (T1, _)) -> true
	| _ -> false
      end in
      
      let in_com1_f = 0 in
      let in_com2_f = 0 in
      let output = ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2_f, eps, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22))) in
      
      if (if_abort = true) then begin
	(* let print output = begin *)
	(*   match (var_in_set V1 rs2), (var_in_set V2 rs2), (var_in_set V1 ws2), (var_in_set V2 ws2) with *)
	(*     | true, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "rdt2v1"; *)
	(* 	print_states_to_file output *)
	(*     | _, true, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "rdt2v2"; *)
	(* 	print_states_to_file output *)
	(*     | _, _, true, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "wrt2v1"; *)
	(* 	print_states_to_file output *)
	(*     | _, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output "wrt2v2"; *)
	(* 	print_states_to_file output *)
	(* end in *)
	(* print output;  *)
	let output_abt = commit_one_t2 (fst(output)) (snd(output)) in
	if eps1 != 0 then output_abt else begin
	  print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_abt "abtt1";
	  output_abt
	end
      end
      
      else begin
	let sta = Committed in
	let rs = (None, None) in
	let ws = (None, None) in
	let rw_cfl = (None, None) in
	let wr_cfl = (None, None) in
	let ww_cfl = (None, None) in
	let output_com = begin
	  match empty_wr with
	  | true -> ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, (None, None), ww_cfl1, (cls11_f, cls12_f)), (sta, flg2, in_com2_f, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f)))
	  | false -> ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11_f, cls12_f)), (sta, flg2, in_com2_f, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))) end in
	if eps1 != 0 then output_com else begin
	  print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)) output_com "comt2";
	  output_com
	end
      end
    end
  end
end

(* let test_st1 = *)
(*   ((Committed, 0, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Active, 0, 0, 0, (None, Some V2), (None, None), (None, None), (None, None), (None, None), (I, E)));; *)
(* let test_st2 = *)
(*   ((Active, 0, 0, 0, (None, Some V2), (None, None), (None, None), (None, None), (None, None), (I, E)), (Committed, 0, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)));; *)

(* let com_one_t2_st = commit_one_t2 (fst(test_st1)) (snd(test_st1));; *)
(* let com_two_t2_st = commit_two_t2 (fst(com_one_t2_st)) (snd(com_one_t2_st));; *)
(* let com_one_t2_str = print_state_pair (fst(com_one_t2_st)) (snd(com_one_t2_st));; *)
(* let com_two_t2_str = print_state_pair (fst(com_two_t2_st)) (snd(com_two_t2_st));; *)
(* printf "The result of commit_one_t2 of the state is:\n %s\n" com_one_t2_str;; *)
(* printf "The result of commit_two_t2 of the state is:\n %s\n" com_two_t2_str;; *)

(* let com_one_t1_st = commit_one_t1 (fst(test_st2)) (snd(test_st2));; *)
(* let com_two_t1_st = commit_two_t1 (fst(com_one_t1_st)) (snd(com_one_t1_st));; *)
(* let com_one_t1_str = print_state_pair (fst(com_one_t1_st)) (snd(com_one_t1_st));; *)
(* let com_two_t1_str = print_state_pair (fst(com_two_t1_st)) (snd(com_two_t1_st));; *)
(* printf "The result of commit_one_t1 of the state is:\n %s\n" com_one_t1_str;; *)
(* printf "The result of commit_two_t1 of the state is:\n %s\n" com_two_t1_str;; *)

let nread_t1_v1 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta1 = Active || flg1 != 0) || flg2 != 0) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls11, cls21 with
      |	M, I -> (cls11, cls21)
      |	E, I -> (cls11, cls21)
      |	S, I -> (cls11, cls21)
      |	S, S -> (cls11, cls21)
      |	S, TI -> (cls11, cls21)
      |	I, TMI -> (cls11, cls21)
      |	I, TI -> (S, TI)
      |	I, I -> (E, I)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let flg1_f = 1 in
      let rs = add_var v rs1 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws2 with
	| true -> ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    ((sta, flg1_f, in_com1, eps1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls1_f, cls12)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls2_f, cls22)))
    end
  end
end

let nread_t1_v2 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta1 = Active || flg1 != 0) || flg2 != 0) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls12, cls22 with
      |	M, I -> (cls12, cls22)
      |	E, I -> (cls12, cls22)
      |	S, I -> (cls12, cls22)
      |	S, S -> (cls12, cls22)
      |	S, TI -> (cls12, cls22)
      |	I, TMI -> (cls12, cls22)
      |	I, TI -> (S, TI)
      |	I, I -> (E, I)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let flg1_f = 1 in
      let rs = add_var v rs1 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws2 with
	| true -> ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    ((sta, flg1_f, in_com1, eps1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls11, cls1_f)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls21, cls2_f)))
    end
  end
end

let nread_t2_v1 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta2 = Active || flg1 != 0) || flg2 != 0) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls21, cls11 with
      |	M, I -> (cls21, cls11)
      |	E, I -> (cls21, cls11)
      |	S, I -> (cls21, cls11)
      |	S, S -> (cls21, cls11)
      |	S, TI -> (cls21, cls11)
      |	I, TMI -> (cls21, cls11)
      |	I, TI -> (S, TI)
      |	I, I -> (E, I)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta =  Active in
      let flg2_f = 1 in
      let rs = add_var v rs2 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws1 with
	| true -> ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls1_f, cls12)), (sta, flg2_f, in_com2, eps2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls2_f, cls22)))
    end
  end
end

let nread_t2_v2 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta2 = Active || flg1 != 0) || flg2 != 0) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls22, cls12 with
      |	M, I -> (cls22, cls12)
      |	E, I -> (cls22, cls12)
      |	S, I -> (cls22, cls12)
      |	S, S -> (cls22, cls12)
      |	S, TI -> (cls22, cls12)
      |	I, TMI -> (cls22, cls12)
      |	I, TI -> (S, TI)
      |	I, I -> (E, I)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta =  Active in
      let flg2_f = 1 in
      let rs = add_var v rs2 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws1 with
	| true -> ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls11, cls1_f)), (sta, flg2_f, in_com2, eps2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls21, cls2_f)))
    end
  end
end

let nwrite_t1_v1 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta1 = Active || flg1 != 0) || flg2 != 0) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls11, cls21 with
      |	M, I -> (cls11, cls21)
      |	E, I -> (M, cls21)
      |	S, I -> (M, cls21)
      |	S, S -> (M, I)
      |	S, TI -> (M, I)
      |	I, TMI -> (TMI, TMI) (* make I change to TMI first since M and TMI cannot exist at the same time *)
      |	I, _ -> (M, I) (* I, TI/M/E/S/I *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let flg1_f = 1 in
      let ws = add_var v ws1 in
      let ((wr_cfl, rw_cfl), flg2_f') =
	match var_in_set v rs2 with
	| true -> (((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2)), 2)
	| _ -> ((wr_cfl1, rw_cfl2), flg2)
      in
      let ((ww_cfl1_f, ww_cfl2_f), flg2_f) =
	match var_in_set v ws2 with
	| true -> (((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)), 2)
	| _ -> ((ww_cfl1, ww_cfl2), flg2_f')
      in
    ((sta, flg1_f, in_com1, eps1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls1_f, cls12)), (sta2, flg2_f, in_com2, eps2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls2_f, cls22)))
    end
  end
end

let nwrite_t1_v2 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta1 = Active || flg1 != 0) || flg2 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls12, cls22 with
      |	M, I -> (cls12, cls22)
      |	E, I -> (M, cls22)
      |	S, I -> (M, cls22)
      |	S, S -> (M, I)
      |	S, TI -> (M, I)
      |	I, TMI -> (TMI, TMI) (* make I change to TMI first since M and TMI cannot exist at the same time *)
      |	I, _ -> (M, I) (* I, TI/M/E/S/I *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let flg1_f = 1 in
      let ws = add_var v ws1 in
      let ((wr_cfl, rw_cfl), flg2_f') =
	match var_in_set v rs2 with
	| true -> (((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2)), 2)
	| _ -> ((wr_cfl1, rw_cfl2), flg2)
      in
      let ((ww_cfl1_f, ww_cfl2_f), flg2_f) =
	match var_in_set v ws2 with
	| true -> (((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)), 2)
	| _ -> ((ww_cfl1, ww_cfl2), flg2_f')
      in
    ((sta, flg1_f, in_com1, eps1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls11, cls1_f)), (sta2, flg2_f, in_com2, eps2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls21, cls2_f)))
    end
  end
end

let nwrite_t2_v1 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta2 = Active || flg1 != 0) || flg2 != 0) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls21, cls11 with
      |	M, I -> (cls21, cls11)
      |	E, I -> (M, cls11)
      |	S, I -> (M, cls11)
      |	S, S -> (M, I)
      |	S, TI -> (M, I)
      |	I, TMI -> (TMI, TMI) (* make I change to TMI first since M and TMI cannot exist at the same time *)
      |	I, _ -> (M,I) (* I, TI/M/E/S/I *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let flg2_f = 1 in
      let ws = add_var v ws2 in
      let ((wr_cfl, rw_cfl), flg1_f') =
	match var_in_set v rs1 with
	| true -> (((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1)), 2)
	| _ -> ((wr_cfl2, rw_cfl1), flg1)
      in
      let ((ww_cfl2_f, ww_cfl1_f), flg1_f) =
	match var_in_set v ws1 with
	| true -> (((add_ci (T2, v) ww_cfl2), (add_ci (T1, v) ww_cfl1)), 2)
	| _ -> ((ww_cfl2, ww_cfl1), flg1_f')
      in
    ((sta1, flg1_f, in_com1, eps1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls1_f, cls12)), (sta, flg2_f, in_com2, eps2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls2_f, cls22)))
    end
  end
end

let nwrite_t2_v2 (v: var) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta2 = Active || flg1 != 0) || flg2 != 0) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls22, cls12 with
      |	M, I -> (cls22, cls12)
      |	E, I -> (M, cls12)
      |	S, I -> (M, cls12)
      |	S, S -> (M, I)
      |	S, TI -> (M, I)
      |	I, TMI -> (TMI, TMI) (* make I change to TMI first since M and TMI cannot exist at the same time *)
      |	I, _ -> (M,I) (* I, TI/M/E/S/I *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let flg2_f = 1 in
      let ws = add_var v ws2 in
      let ((wr_cfl, rw_cfl), flg1_f') =
	match var_in_set v rs1 with
	| true -> (((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1)), 2)
	| _ -> ((wr_cfl2, rw_cfl1), flg1)
      in
      let ((ww_cfl2_f, ww_cfl1_f), flg1_f) =
	match var_in_set v ws1 with
	| true -> (((add_ci (T2, v) ww_cfl2), (add_ci (T1, v) ww_cfl1)), 2)
	| _ -> ((ww_cfl2, ww_cfl1), flg1_f')
      in
    ((sta1, flg1_f, in_com1, eps1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls11, cls1_f)), (sta, flg2_f, in_com2, eps2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls21, cls2_f)))
    end
  end
end

let nabort_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta1 != Invalid || flg1 != 2) || flg2 != 1) || in_com2 != 0) then non_exist
  else begin
    let (cls11_f, cls21_f) =
      match cls11, cls21 with
      | TMI, TMI -> (I, cls21)
      | TMI, I -> (I, cls21)
      |	_, _ -> (cls11, cls21)
    in
    let (cls12_f, cls22_f) =
      match cls12, cls22 with
      | TMI, TMI -> (I, cls22)
      | TMI, I -> (I, cls22)
      |	_, _ -> (cls12, cls22)
    in
    let sta = Aborted in
    let flg = 0 in
    let rs = (None, None) in
    let ws = (None, None) in
    let rw_cfl = (None, None) in
    let wr_cfl = (None, None) in
    let ww_cfl = (None, None) in
    ((sta, flg, 0, eps1, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, 0, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21_f, cls22_f)))
  end
end

let nabort_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta2 != Invalid || flg2 != 2) || flg1 != 1) || in_com1 != 0) then non_exist
  else begin
    let (cls21_f, cls11_f) =
      match cls21, cls11 with
      | TMI, TMI -> (I, cls11)
      | TMI, I -> (I, cls11)
      |	_, _ -> (cls21, cls11)
    in
    let (cls22_f, cls12_f) =
      match cls22, cls12 with
      | TMI, TMI -> (I, cls12)
      | TMI, I -> (I, cls12)
      |	_, _ -> (cls22, cls12)
    in
    let sta = Aborted in
    let flg = 0 in
    let rs = (None, None) in
    let ws = (None, None) in
    let rw_cfl = (None, None) in
    let wr_cfl = (None, None) in
    let ww_cfl = (None, None) in
    ((sta1, flg1, 0, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11_f, cls12_f)), (sta, flg, 0, eps2, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f)))
  end
end

let ncommit_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta1 != Active || flg1 != 1) || in_com1 != 0) then non_exist
  else begin
    let (cls11_f, cls21_f) =
      match cls11, cls21 with
      | TMI, TMI -> (M, I)
      |	_, _ -> (cls11, cls21) (* there is only one case that the cache line state should be changed after a non-tx read/write. All the other cases keep the cache line states unchaged *)
    in
    let (cls12_f, cls22_f) =
      match cls12, cls22 with
      | TMI, TMI -> (M, I)
      |	_, _ -> (cls12, cls22) (* there is only one case that the cache line state should be changed after a non-tx read/write. All the other cases keep the cache line states unchaged *)
    in
    
    let flg = 0 in
    let sta = Committed in
    let rs = (None, None) in
    let ws = (None, None) in
    let rw_cfl = (None, None) in
    let wr_cfl = (None, None) in
    let ww_cfl = (None, None) in
      
    (* let naborted_part = snd (nabort_t2 (sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in *)
    let abt_cls21 = fst(naborted_cls cls21 cls11) in
    let abt_cls22 = fst(naborted_cls cls22 cls12) in
    let invalid_state = (Invalid, 0, 0, eps2, (None, None), (None, None), (None, None), (None, None), (None, None), (abt_cls21, abt_cls22)) in
    if flg2 = 2 then ((sta, flg, 0, eps1, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), invalid_state)
    else ((sta, flg, 0, eps1, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21_f, cls22_f)))
  end
end

let ncommit_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta2 != Active || flg2 != 1) || in_com2 != 0) then non_exist
  else begin
    let (cls21_f, cls11_f) =
      match cls21, cls11 with
      | TMI, TMI -> (M, I)
      |	_, _ -> (cls21, cls11) (* there is only one case that the cache line state should be changed after a non-tx read/write. All the other cases keep the cache line states unchaged *)
    in
    let (cls22_f, cls12_f) =
      match cls22, cls12 with
      | TMI, TMI -> (M, I)
      |	_, _ -> (cls22, cls12) (* there is only one case that the cache line state should be changed after a non-tx read/write. All the other cases keep the cache line states unchaged *)
    in
    
    let flg = 0 in
    let sta = Committed in
    let rs = (None, None) in
    let ws = (None, None) in
    let rw_cfl = (None, None) in
    let wr_cfl = (None, None) in
    let ww_cfl = (None, None) in
      
    (* let naborted_part = fst (nabort_t1 (sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in *)
    let abt_cls11 = fst(naborted_cls cls11 cls21) in
    let abt_cls12 = fst(naborted_cls cls12 cls22) in
    let invalid_state = (Invalid, 0, 0, eps1, (None, None), (None, None), (None, None), (None, None), (None, None), (abt_cls11, abt_cls12)) in
    if flg1 = 2 then (invalid_state, (sta, flg, in_com2, eps2, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f)))
    else ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11_f, cls12_f)), (sta, flg, 0, eps2, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f)))
  end
end

let get_flg state = begin
  match state with
  | (_, flg, _, _,  _, _, _, _, _, _) -> flg
end

let get_in_com state = begin
  match state with
  | (_, _, in_com, _,  _, _, _, _, _, _) -> in_com
end

let get_eps state = begin
  match state with
  | (_, _, _, eps,  _, _, _, _, _, _) -> eps
end

let zero_eps ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state)  = begin
  ((sta1, flg1, in_com1, 0, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)), (sta2, flg2, in_com2, 0, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)))
end

let get_pre_t1 state1 state2 post_state trans_str tbl_str = begin
  let pre =
    try
      Eps_trans.find eps_trans ((state1, state2), "com_one, t1")
    with Not_found -> non_exist 
  in
  let post_zero = zero_eps (fst(post_state)) (snd(post_state)) in
  print_to_files (fst(pre)) (snd(pre)) post_zero trans_str;
  if pre = non_exist then printf "The pre_t1 state of \n%s \nis non_exist: \n" (print_state_pair state1 state2);
  print_states_to_file post_zero;
  Forward.add forward ((state1, state2), tbl_str) post_zero;
  post_zero
end

let get_pre_t2 state1 state2 post_state trans_str tbl_str = begin
  let pre =
    try
      Eps_trans.find eps_trans ((state1, state2), "com_one, t2")
    with Not_found -> non_exist
  in
  let post_zero = zero_eps (fst(post_state)) (snd(post_state)) in
  print_to_files (fst(pre)) (snd(pre)) post_zero trans_str;
  if pre = non_exist then printf "The pre_t2 state of \n%s \nis non_exist: \n" (print_state_pair state1 state2);
  print_states_to_file post_zero;
  Forward.add forward ((state1, state2), tbl_str) post_zero;
  post_zero
end

let get_pre_both state1 state2 post_state trans_str tbl_str = begin
  let pre'' =
    try
      Eps_trans.find eps_trans ((state1, state2), "com_one, t2")
    with Not_found -> non_exist
  in
  let pre = begin
    if (pre'' == non_exist) then begin
      let pre' =
  	try
  	  Eps_trans.find eps_trans ((state1, state2), "com_one, t1")
  	with Not_found -> begin
  	  printf "The pre state of com_one, t1 is not found: %s\n" (print_state_pair state1 state2);
  	  non_exist
  	end
      in
      try
  	Eps_trans.find eps_trans (((fst(pre')), (snd(pre'))), "com_one, t2")
      with Not_found -> begin
  	printf "The pre state of com_one, t2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  	non_exist
      end
    end
    else begin
      try
  	Eps_trans.find eps_trans (((fst(pre'')), (snd(pre''))), "com_one, t1")
      with Not_found ->  begin
  	printf "The pre state of com_one, t1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  	non_exist
      end
    end
  end in
  let post_zero = zero_eps (fst(post_state)) (snd(post_state)) in
  print_to_files (fst(pre)) (snd(pre)) post_zero trans_str;
  print_states_to_file post_zero;
  Forward.add forward ((state1, state2), tbl_str) post_zero;
  post_zero
end

(* let get_pre_com_two_t1 state1 state2 post_state tbl_str = begin *)
(*   let pre = *)
(*     try *)
(*       Eps_trans.find eps_trans ((state1, state2), "com_one, t1") *)
(*     with Not_found -> non_exist  *)
(*   in *)
(*   let post_zero = zero_eps (fst(post_state)) (snd(post_state)) in *)
(*   print_states_to_file post_zero; *)
(*   Forward.add forward ((state1, state2), tbl_str) post_zero; *)
(*   post_zero *)
(* end *)



let inv_to_abt (sta, flg, in_com, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls) = begin
  let sta_f = Aborted in
  (sta_f, flg, in_com, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls)
end

let ref_loop = ref 0;;

print_states_to_file init_state_pair;;

let get_post_state state1 state2 = begin
  let after_tread_t1_v1 =
    try
      Forward.find forward ((state1, state2), "tx, rd, t1, v1")
    with Not_found ->
      let post_state = tread_t1_v1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt1v1";
	      if (state1, state2) = non_exist
		  then printf "The input state \n%s \nis non_exist. \n" (print_state_pair state1 state2);
  	      Forward.add forward ((state1, state2), "tx, rd, t1, v1") post_state;
  	      print_states_to_file post_state;
  	      post_state
  	  end
  	  | (_, 0) -> get_pre_t1 state1 state2 post_state "rdt1v1" "tx, rd, t1, v1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "rdt1v1" "tx, rd, t1, v1"
	  | (_, _) -> get_pre_both state1 state2 post_state "rdt1v1" "tx, rd, t1, v1"
      end
  in
  	  (* printf "No. %d: after_tread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t1_v1)) (snd(after_tread_t1_v1))); *)

  let after_tread_t1_v2 =
    try
      Forward.find forward ((state1, state2), "tx, rd, t1, v2")
    with Not_found ->
      let post_state = tread_t1_v2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt1v2";
  	      Forward.add forward ((state1, state2), "tx, rd, t1, v2") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | (_, 0) -> get_pre_t1 state1 state2 post_state "rdt1v2" "tx, rd, t1, v2"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "rdt1v2" "tx, rd, t1, v2"
	  | (_, _) -> get_pre_both state1 state2 post_state "rdt1v2" "tx, rd, t1, v2"
      end
  in
  	  (* printf "No. %d: after_tread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t1_v2)) (snd(after_tread_t1_v2))); *)

  let after_tread_t2_v1 =
    try
      Forward.find forward ((state1, state2), "tx, rd, t2, v1")
    with Not_found ->
      let post_state = tread_t2_v1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt2v1";
  	      Forward.add forward ((state1, state2), "tx, rd, t2, v1") post_state;
  	      print_states_to_file post_state;
  	      post_state
        end
  	  | (_, 0) -> get_pre_t1 state1 state2 post_state "rdt2v1" "tx, rd, t2, v1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "rdt2v1" "tx, rd, t2, v1"
	  | (_, _) -> get_pre_both state1 state2 post_state "rdt2v1" "tx, rd, t2, v1"
      end
  in
  	  (* printf "No. %d: after_tread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t2_v1)) (snd(after_tread_t2_v1))); *)

  let after_tread_t2_v2 =
    try
      Forward.find forward ((state1, state2), "tx, rd, t2, v2")
    with Not_found ->
      let post_state = tread_t2_v2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt2v2";
  	      Forward.add forward ((state1, state2), "tx, rd, t2, v2") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | (_, 0) -> get_pre_t1 state1 state2 post_state "rdt2v2" "tx, rd, t2, v2"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "rdt2v2" "tx, rd, t2, v2"
	  | (_, _) -> get_pre_both state1 state2 post_state "rdt2v2" "tx, rd, t2, v2"
      end
  in
  	  (* printf "No. %d: after_tread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t2_v2)) (snd(after_tread_t2_v2))); *)

  let after_twrite_t1_v1 =
    try
      Forward.find forward ((state1, state2), "tx, wr, t1, v1")
    with Not_found ->
      let post_state = twrite_t1_v1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt1v1";
  	      Forward.add forward ((state1, state2), "tx, wr, t1, v1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | (_, 0) -> get_pre_t1 state1 state2 post_state "wrt1v1" "tx, wr, t1, v1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "wrt1v1" "tx, wr, t1, v1"
	  | (_, _) -> get_pre_both state1 state2 post_state "wrt1v1" "tx, wr, t1, v1"
      end
  in
  	  (* printf "No. %d: after_twrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t1_v1)) (snd(after_twrite_t1_v1))); *)

  let after_twrite_t1_v2 =
    try
      Forward.find forward ((state1, state2), "tx, wr, t1, v2")
    with Not_found ->
      let post_state = twrite_t1_v2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt1v2";
  	      Forward.add forward ((state1, state2), "tx, wr, t1, v2") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | (_, 0) -> get_pre_t1 state1 state2 post_state "wrt1v2" "tx, wr, t1, v2"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "wrt1v2" "tx, wr, t1, v2"
	  | (_, _) -> get_pre_both state1 state2 post_state "wrt1v2" "tx, wr, t1, v2"
      end
  in
  	  (* printf "No. %d: after_twrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t1_v2)) (snd(after_twrite_t1_v2))); *)

  let after_twrite_t2_v1 =
    try
      Forward.find forward ((state1, state2), "tx, wr, t2, v1")
    with Not_found ->
      let post_state = twrite_t2_v1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt2v1";
  	      Forward.add forward ((state1, state2), "tx, wr, t2, v1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | (_, 0) -> get_pre_t1 state1 state2 post_state "wrt2v1" "tx, wr, t2, v1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "wrt2v1" "tx, wr, t2, v1"
	  | (_, _) -> get_pre_both state1 state2 post_state "wrt2v1" "tx, wr, t2, v1"
      end
  in
  	  (* printf "No. %d: after_twrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t2_v1)) (snd(after_twrite_t2_v1))); *)

  let after_twrite_t2_v2 =
    try
      Forward.find forward ((state1, state2), "tx, wr, t2, v2")
    with Not_found ->
      let post_state = twrite_t2_v2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt2v2";
  	      Forward.add forward ((state1, state2), "tx, wr, t2, v2") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | (_, 0) -> get_pre_t1 state1 state2 post_state "wrt2v2" "tx, wr, t2, v2"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "wrt2v2" "tx, wr, t2, v2"
	  | (_, _) -> get_pre_both state1 state2 post_state "wrt2v2" "tx, wr, t2, v2"
      end
  in
  	  (* printf "No. %d: after_twrite_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t2_v2)) (snd(after_twrite_t2_v2))); *)

(*   let after_abt_t1 = *)
(*     try *)
(*       Forward.find forward ((state1, state2), "tx, abt, t1") *)
(*     with Not_found -> *)
(*       let post_state = abort_t1 state1 state2 in *)
(*       match check_status post_state 1 with *)
(*       |	Non_exist -> post_state *)
(*       |	_ -> begin *)
(*   	  print_to_files state1 state2 post_state "abtt1"; *)
(*   	  Forward.add forward ((state1, state2), "tx, abt, t1") post_state; *)
(*   	  print_states_to_file post_state; *)
(*   	  post_state *)
(*         end *)
(*   in *)
(*   	  (\* printf "No. %d: after_abt_t1\n%s\n" (!state_no) (print_state_pair (fst(after_abt_t1)) (snd(after_abt_t1))); *\) *)

(*   let after_abt_t2 = *)
(*     try *)
(*       Forward.find forward ((state1, state2), "tx, abt, t2") *)
(*     with Not_found -> *)
(*       let post_state = abort_t2 state1 state2 in *)
(*       match check_status post_state 1 with *)
(*       |	Non_exist -> post_state *)
(*       |	_ -> begin *)
(*   	  print_to_files state1 state2 post_state "abtt2"; *)
(*   	  Forward.add forward ((state1, state2), "tx, abt, t2") post_state; *)
(*   	  print_states_to_file post_state; *)
(*   	  post_state *)
(*         end *)
(*   in *)
(*   	  (\* printf "No. %d: after_abt_t2\n%s\n" (!state_no) (print_state_pair (fst(after_abt_t2)) (snd(after_abt_t2))); *\) *)

(* no need to check pre_t2 of after_com_one_t1 or after_com_two_t2, otherwise there would be no need to check pre_both of the other functions *)

  let after_com_one_t1 =
    try
      Forward.find forward ((state1, state2), "tx, com_one, t1")
    with Not_found ->
      let post_state = commit_one_t1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  (* print_to_files state1 state2 post_state "comt1"; *)
  	  Forward.add forward ((state1, state2), "tx, com_one, t1") post_state;
  	  print_states_to_file post_state;
  	  post_state
        end
  in
  	  (* printf "No. %d: after_com_one_t1 of\n%s is:\n%s\n" (!state_no) (print_state_pair state1 state2) (print_state_pair (fst(after_com_one_t1)) (snd(after_com_one_t1))); *)

  let after_com_one_t2 =
    try
      Forward.find forward ((state1, state2), "tx, com_one, t2")
    with Not_found ->
      let post_state = commit_one_t2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  (* print_to_files state1 state2 post_state "comt2"; *)
  	  Forward.add forward ((state1, state2), "tx, com_one, t2") post_state;
  	  print_states_to_file post_state;
  	  post_state
        end
  in
  	  (* printf "No. %d: after_com_one_t2\n%s\n" (!state_no) (print_state_pair (fst(after_com_one_t2)) (snd(after_com_one_t2))); *)

  let after_com_two_t1 =
    try
      Forward.find forward ((state1, state2), "tx, com_two, t1")
    with Not_found ->
      let post_state = commit_two_t1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
	    (* eps1 must be zero so no need to check *)
	  | 0 -> begin
  	      (* print_to_files state1 state2 post_state "comt1"; *)
  	      Forward.add forward ((state1, state2), "tx, com_two, t1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> begin
	      match (get_status (fst(post_state))) with
	      |	Committed -> get_pre_t2 state1 state2 post_state "comt1" "tx, com_two, t1"
	      |	_ -> get_pre_t2 state1 state2 post_state "abtt2" "tx, com_two, t1"  
              (* else status2 is Aborted. Not checking if status1 is aborted because the output of com_two can be (aborted, committed) with the transition comt2 *)
	  end
      end
  in
  	  (* printf "No. %d: after_com_two_t1 of\n%s is:\n%s\n" (!state_no) (print_state_pair state1 state2) (print_state_pair (fst(after_com_two_t1)) (snd(after_com_two_t1))); *)

  let after_com_two_t2 =
    try
      Forward.find forward ((state1, state2), "tx, com_two, t2")
    with Not_found ->
      let post_state = commit_two_t2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
  	      (* print_to_files state1 state2 post_state "comt2"; *)
  	      Forward.add forward ((state1, state2), "tx, com_two, t2") post_state;
  	      print_states_to_file post_state;
  	      post_state
  	  end
  	  | _ -> begin
  	      match (get_status (snd(post_state))) with
	      |	Committed -> get_pre_t1 state1 state2 post_state "comt2" "tx, com_two, t2"
  	      |	_ -> get_pre_t1 state1 state2 post_state "abtt1" "tx, com_two, t2"
  	  end
      end
  in
  	  (* printf "No. %d: after_com_two_t2\n%s\n" (!state_no) (print_state_pair (fst(after_com_two_t2)) (snd(after_com_two_t2))); *)

  let nrd_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v1")
    with Not_found ->
      let post_state = nread_t1_v1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "rdt1v1";
  	      Forward.add forward ((state1, state2), "nt, rd, t1, v1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> get_pre_t2 state1 state2 post_state "rdt1v1" "nt, rd, t1, v1"
      end
  in
  	  (* printf "No. %d: nrd_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(nrd_t1_v1)) (snd(nrd_t1_v1))); *)

  let after_nread_t1_v1 =
    if (check_status nrd_t1_v1 1) = Non_exist then non_exist
    else begin
      let st1 = fst(nrd_t1_v1) in
      let st2 = snd(nrd_t1_v1) in
      try
  	Forward.find forward ((st1, st2), "nt, com, t1")
      with Not_found ->
  	let post_state = ncommit_t1 st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "comt1";
  	    Forward.add forward ((st1, st2), "nt, com, t1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_nread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t1_v1)) (snd(after_nread_t1_v1))); *)

  let nrd_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v2")
    with Not_found ->
      let post_state = nread_t1_v2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "rdt1v2";
  	      Forward.add forward ((state1, state2), "nt, rd, t1, v2") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> get_pre_t2 state1 state2 post_state "rdt1v2" "nt, rd, t1, v2"
      end
  in
  	  (* printf "No. %d: nrd_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(nrd_t1_v2)) (snd(nrd_t1_v2))); *)

  let after_nread_t1_v2 =
    if (check_status nrd_t1_v2 1) = Non_exist then non_exist
    else begin
      let st1 = fst(nrd_t1_v2) in
      let st2 = snd(nrd_t1_v2) in
      try
  	Forward.find forward ((st1, st2), "nt, com, t1")
      with Not_found ->
  	let post_state = ncommit_t1 st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "comt1";
  	    Forward.add forward ((st1, st2), "nt, com, t1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_nread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t1_v2)) (snd(after_nread_t1_v2))); *)

  let nrd_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v1")
    with Not_found ->
      let post_state = nread_t2_v1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "rdt2v1";
  	      Forward.add forward ((state1, state2), "nt, rd, t2, v1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> get_pre_t1 state1 state2 post_state "rdt2v1" "nt, rd, t2, v1"
      end
  in
  	  (* printf "No. %d: nrd_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(nrd_t2_v1)) (snd(nrd_t2_v1))); *)

  let after_nread_t2_v1 =
    if (check_status nrd_t2_v1 1) = Non_exist then non_exist
    else begin
      let st1 = fst(nrd_t2_v1) in
      let st2 = snd(nrd_t2_v1) in
      try
  	Forward.find forward ((st1, st2), "nt, com, t2")
      with Not_found ->
  	let post_state = ncommit_t2 st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "comt2";
  	    Forward.add forward ((st1, st2), "nt, com, t2") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_nread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t2_v1)) (snd(after_nread_t2_v1))); *)

  let nrd_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v2")
    with Not_found ->
      let post_state = nread_t2_v1 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "rdt2v2";
  	      Forward.add forward ((state1, state2), "nt, rd, t2, v2") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> get_pre_t1 state1 state2 post_state "rdt2v2" "nt, rd, t2, v2"
      end
  in
  	  (* printf "No. %d: nrd_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(nrd_t2_v2)) (snd(nrd_t2_v2))); *)

  let after_nread_t2_v2 =
    if (check_status nrd_t2_v2 1) = Non_exist then non_exist
    else begin
      let st1 = fst(nrd_t2_v2) in
      let st2 = snd(nrd_t2_v2) in
      try
  	Forward.find forward ((st1, st2), "nt, com, t2")
      with Not_found ->
  	let post_state = ncommit_t2 st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "comt2";
  	    Forward.add forward ((st1, st2), "nt, com, t2") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_nread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t2_v2)) (snd(after_nread_t2_v2))); *)

  let nwr_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v1")
    with Not_found ->
      let post_state = nwrite_t1_v1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "wrt1v1";
  	      Forward.add forward ((state1, state2), "nt, wr, t1, v1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> get_pre_t2 state1 state2 post_state "wrt1v1" "nt, wr, t1, v1"
      end
  in
  	  (* printf "No. %d: nwr_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(nwr_t1_v1)) (snd(nwr_t1_v1))); *)

  let after_nwrite_t1_v1 =
    if (check_status nwr_t1_v1 1) = Non_exist then non_exist
    else begin
      let st1 = fst(nwr_t1_v1) in
      let st2 = snd(nwr_t1_v1) in
      try
  	Forward.find forward ((st1, st2), "nt, com, t1")
      with Not_found ->
  	let post_state = ncommit_t1 st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "comt1";
  	    Forward.add forward ((st1, st2), "nt, com, t1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_nwrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t1_v1)) (snd(after_nwrite_t1_v1))); *)

  let nwr_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v2")
    with Not_found ->
      let post_state = nwrite_t1_v2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "wrt1v2";
  	      Forward.add forward ((state1, state2), "nt, wr, t1, v2") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> get_pre_t2 state1 state2 post_state "wrt1v2" "nt, wr, t1, v2"
      end
  in
  	  (* printf "No. %d: nwr_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(nwr_t1_v2)) (snd(nwr_t1_v2))); *)

  let after_nwrite_t1_v2 =
    if (check_status nwr_t1_v2 1) = Non_exist then non_exist
    else begin
      let st1 = fst(nwr_t1_v2) in
      let st2 = snd(nwr_t1_v2) in
      try
  	Forward.find forward ((st1, st2), "nt, com, t1")
      with Not_found ->
  	let post_state = ncommit_t1 st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "comt1";
  	    Forward.add forward ((st1, st2), "nt, com, t1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_nwrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t1_v2)) (snd(after_nwrite_t1_v2))); *)

  let nwr_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v1")
    with Not_found ->
      let post_state = nwrite_t2_v1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "wrt2v1";
  	      Forward.add forward ((state1, state2), "nt, wr, t2, v1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> get_pre_t1 state1 state2 post_state "wrt2v1" "nt, wr, t2, v1"
      end
  in
  	  (* printf "No. %d: nwr_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(nwr_t2_v1)) (snd(nwr_t2_v1))); *)

  let after_nwrite_t2_v1 =
    if (check_status nwr_t2_v1 1) = Non_exist then non_exist
    else begin
      let st1 = fst(nwr_t2_v1) in
      let st2 = snd(nwr_t2_v1) in
      try
  	Forward.find forward ((st1, st2), "nt, com, t2")
      with Not_found ->
  	let post_state = ncommit_t2 st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "comt2";
  	    Forward.add forward ((st1, st2), "nt, com, t2") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_nwrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t2_v1)) (snd(after_nwrite_t2_v1))); *)

  let nwr_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v2")
    with Not_found ->
      let post_state = nwrite_t2_v2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "wrt2v2";
  	      Forward.add forward ((state1, state2), "nt, wr, t2, v2") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
  	  | _ -> get_pre_t1 state1 state2 post_state "wrt2v2" "nt, wr, t2, v2"
      end
  in
  	  (* printf "No. %d: nwr_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(nwr_t2_v2)) (snd(nwr_t2_v2))); *)

  let after_nwrite_t2_v2 =
    if (check_status nwr_t2_v2 1) = Non_exist then non_exist
    else begin
      let st1 = fst(nwr_t2_v2) in
      let st2 = snd(nwr_t2_v2) in
      try
  	Forward.find forward ((st1, st2), "nt, com, t2")
      with Not_found ->
  	let post_state = ncommit_t2 st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "comt2";
  	    Forward.add forward ((st1, st2), "nt, com, t2") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_nwrite_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t2_v2)) (snd(after_nwrite_t2_v2))); *)

  let state_list = [after_tread_t1_v1; after_tread_t1_v2; after_tread_t2_v1; after_tread_t2_v2; after_twrite_t1_v1; after_twrite_t1_v2; after_twrite_t2_v1; after_twrite_t2_v2;
		    (* after_abt_t1; after_abt_t2; *) after_com_one_t1; after_com_one_t2; after_com_two_t1; after_com_two_t2; after_nread_t1_v1; after_nread_t1_v2; after_nread_t2_v1; after_nread_t2_v2; after_nwrite_t1_v1;
		    after_nwrite_t1_v2; after_nwrite_t2_v1; after_nwrite_t2_v2;
		   ] in
  let stateSet = StateSet.empty in
  let newStateSet = List.fold_left (fun acc st -> StateSet.add st acc) stateSet state_list in
  let postStateSet = StateSet.remove non_exist newStateSet in
  (* let finalSet = StateSet.remove *)
  (*     ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
  (*     newStateSet in *)
  let newList = StateSet.elements postStateSet in
  (* let newList = StateSet.elements finalSet in *)
  let postStateList = List.fold_left (fun acc (st:statePair) ->
    begin
      let proc_st =
	match (check_status st 1), (check_status st 2) with
	| Invalid, _ -> begin
	    match get_flg (fst(st)) with
	    | 0 -> begin
		try
		  Forward.find forward (st, "tx, abt, t1")
		with Not_found ->
		  let aborted = inv_to_abt (fst(st)) in
		  let aborted_st = (aborted, snd(st)) in
		  print_to_files (fst(st)) (snd(st)) aborted_st "abtt1";
		  print_states_to_file st;
		  print_states_to_file aborted_st;
		  Forward.add forward (st, "tx, abt, t1") aborted_st;
		  aborted_st
	      end
	    | _ -> begin
		try
		  Forward.find forward (st, "nt, abt, t1")
		with Not_found ->
		  let naborted = inv_to_abt (fst(st)) in
		  let naborted_st = (naborted, snd(st)) in
		  print_to_files (fst(st)) (snd(st)) naborted_st "abtt1";
		  print_states_to_file st;
		  print_states_to_file naborted_st;
		  Forward.add forward (st, "nt, abt, t1") naborted_st;
		  naborted_st
	      end
	  end
	| _, Invalid -> begin
	    match get_flg (snd(st)) with
	    | 0 -> begin
		try
		  Forward.find forward (st, "tx, abt, t2")
		with Not_found ->
		  let aborted = inv_to_abt (snd(st)) in
		  let aborted_st = (fst(st), aborted) in
		  print_to_files (fst(st)) (snd(st)) aborted_st "abtt2";
		  print_states_to_file st;
		  print_states_to_file aborted_st;
		  Forward.add forward (st, "tx, abt, t2") aborted_st;
		  aborted_st
	      end
	    | _ -> begin
		try
		  Forward.find forward (st, "nt, abt, t2")
		with Not_found ->
		  let naborted = inv_to_abt (snd(st)) in
		  let naborted_st = (fst(st), naborted) in
		  print_to_files (fst(st)) (snd(st)) naborted_st "abtt2";
		  print_states_to_file st;
		  print_states_to_file naborted_st;
		  Forward.add forward (st, "nt, abt, t2") naborted_st;
		  naborted_st
	      end
	  end
	| _, _ -> st
	in proc_st::acc end) [] newList
      in

  let rec get_final postList finalList = begin
    match postList, finalList with
    | [], fl -> fl
    | hd::tl, fl -> begin
	match (get_in_com (fst(hd))), (get_in_com (snd(hd))) with
	| 0, 0 -> get_final tl (hd::fl)
	| _, _ -> get_final tl fl
	end
  end in
  
  let finalList = get_final postStateList [] in

  (* ref_loop := (!ref_loop) + 1; *)
  (* printf "loop %d: \n" (!ref_loop); *)
  (* printf "The post states of %s are:\n" (print_state_pair state1 state2); *)
  (* List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) finalList; *)
  (* printf "\n"; *)

  (postStateList, finalList)
end

let rec reachable work_list visit_list finalSet = begin
  match work_list, visit_list, finalSet with
  | [], v, fs -> fs
  | hd::tl, v, fs -> begin
      let new_v = hd::v in
      let post_w = fst(get_post_state (fst(hd)) (snd(hd))) in                                   (* get the post states list *)
      let finalStates = snd(get_post_state (fst(hd)) (snd(hd))) in                              (* new *)
      let emptySet = StateSet.empty in
      let finalSet = List.fold_left (fun acc st -> StateSet.add st acc) fs finalStates in       (* new *)
      let visitSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet new_v in
      let oldWorkSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet tl in
      let oldSet = StateSet.union visitSet oldWorkSet in
      let postSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet post_w in
      let newStates = StateSet.diff postSet oldSet in
      let newWorkList = StateSet.elements (StateSet.union oldWorkSet newStates) in
      reachable newWorkList new_v finalSet
  end
end
;;

let visit_ref = ref (StateSet.empty)
let visitSet = reachable [init_state_pair] [] (!visit_ref);;
let visited = StateSet.elements visitSet;;
let size = List.length visited;;
printf ("The number of the final states is %d\n") size;;
printf ("The number of the states is %d\n") (!state_no);;

let rec print_state_file stateList oc = begin
  match stateList with
  | [] -> close_out oc
  | hd::tl -> begin
      let hd_str = print_state_pair (fst(hd)) (snd(hd)) in
      let pol_hd = polish_state "" hd_str in
      fprintf oc "%s\n" pol_hd;
      print_state_file tl oc
  end
end;;

print_state_file visited o_f;;
(* print_state_file visited o_s;; *)
close_out o_s;;
close_out o_t;;

(*let w_file = "../../huml-new/new_read_epsilon_TMESI_two_cache_line.ml"*)
let w_file = "new_read_epsilon_TMESI_two_cache_line.ml"
let i_t = open_in t_file
let i_f = open_in f_file
let i_s = open_in s_file
let o_w = open_out w_file;;

fprintf o_w "Ops\ni:0\n";;

let t_list =["rdt1v1"; "rdt1v2"; "rdt2v1"; "rdt2v2"; "wrt1v1"; "wrt1v2"; "wrt2v1"; "wrt2v2"; "comt1"; "comt2"; "abtt1"; "abtt2"]
let arg_list = List.fold_left (fun acc hd -> ((hd ^ ": 1")::acc)) [] t_list;;
List.iter (fun arg -> fprintf o_w "%s\n" arg) arg_list;;
fprintf o_w "\nAutomaton TMESI\n\n";;

let rec copy_to_file i_ch o_ch = begin
  try
    let get_line = input_line i_ch in
    fprintf o_ch "%s\n" get_line;
    copy_to_file i_ch o_ch
  with End_of_file ->
    fprintf o_ch "\n";
    close_in i_ch
end;;

copy_to_file i_s o_w;;
copy_to_file i_f o_w;;
copy_to_file i_t o_w;;

close_out o_w;;


(* (\********** THE BEGINNING OF THE TESTING CODING **********\) *)
(* let rec run_word word_list state_pair = begin *)
(*   match word_list with *)
(*   | [] -> state_pair *)
(*   | hd::tl -> *)
(*       let post_state = *)
(* 	match hd with *)
(* 	| "tx, rd, t1, v1" -> tread_t1 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, rd, t1, v2" -> tread_t1 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, rd, t2, v1" -> tread_t2 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, rd, t2, v2" -> tread_t2 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, wr, t1, v1" -> twrite_t1 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, wr, t1, v2" -> twrite_t1 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, wr, t2, v1" -> twrite_t2 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, wr, t2, v2" -> twrite_t2 V2 (fst(state_pair)) (snd(state_pair)) *)

(* 	| "tx, abt, t1" -> abort_t1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, abt, t2" -> abort_t2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, com, t1" -> commit_t1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "tx, com, t2" -> commit_t2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, rd, t1, v1" -> nread_t1 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, rd, t1, v2" -> nread_t1 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, rd, t2, v1" -> nread_t2 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, rd, t2, v2" -> nread_t2 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, wr, t1, v1" -> nwrite_t1 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, wr, t1, v2" -> nwrite_t1 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, wr, t2, v1" -> nwrite_t2 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, wr, t2, v2" -> nwrite_t2 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, abt, t1" -> nabort_t1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, abt, t2" -> nabort_t2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "nt, com, t1" -> ncommit_t1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| _ -> ncommit_t2 (fst(state_pair)) (snd(state_pair)) (\* i.e., "nt, com, t2" *\) *)
(*       in *)
(*       run_word tl post_state *)
(* end *)

(* let pre_st = ((Active, 2, (None, None), (None, None), (None, None), (None, None), (None, None), M), (Invalid, 0, (None, None), (None, None), (None, None), (None, None), (None, None), I));; *)
(* let word_result = run_word ["tx, rd, t1, v1"; "tx, rd, t1, v2"; "tx, rd, t2, v1"; "tx, rd, t2, v2"; *)
(* 			    "tx, wr, t1, v1"; "tx, rd, t1, v2"; "tx, rd, t1, v1"; "tx, rd, t1, v2";(\* "tx, rd, t2, v1"; "tx, rd, t1, v1"; *\) *)
(* 			    "tx, com, t1"; (\* "tx, abt, t2" "tx, rd, t2, v1"; "tx, rd, t2, v2"; "tx, com, t1" *\)] init_state_pair *)
(* let word_result_str = print_state_pair (fst(word_result)) (snd(word_result));; *)
(* printf "The result of running a word is:\n %s\n" word_result_str;; *)

(* let inv_st = *)
(*   ((Committed, 0, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Active, 0, 0, 0, (None, Some V2), (None, None), (None, None), (None, None), (None, None), (I, E)));; *)
(*              (\* ((Active, 0, 0, 0, (None, None), (None, V2), (None, None), (None, None), (T2, V2), (I, TMI)), (Active, 0, 0, 0, (None, None), (V1, V2), (None, None), (None, None), (T1, V2), (TMI, TMI))) *\) *)
(* let abt_inv = commit_one_t1 (fst(inv_st)) (snd(inv_st));; *)
(* let abt_inv_str = print_state_pair (fst(abt_inv)) (snd(abt_inv));; *)
(* printf "The result of commit_one_t1 of the good state is:\n %s\n" abt_inv_str;; *)
(* (\********** THE END OF THE TESTING CODING **********\) *)
 

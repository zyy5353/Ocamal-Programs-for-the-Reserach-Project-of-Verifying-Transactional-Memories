(* TMESI automaton with nonatomic committing procedure, namely in lazy mode, with both variables on the only cache line *)

open Printf

type status =  Active | Aborted | Committed | Invalid | Non_exist
(* type trans = TRead | NRead | TWrite | NWrite | Commit | Abort *)
type var = V1 | V2
type thread = T1 | T2
type cl = CL1 (* Same cache lines in different threads have the same name. Here there is only one cache line per thread *)
type flag = int
type in_com = int (* 0 if the transaction is not in the procedure of commit and >0 otherwise *)
type eps = int
type cl_info = thread * cl
type rw_cfl = cl_info option (* Read-write conflict. Here the variable is not included, since only thread and cache line will be checked while aborting or commiting a transaction *)
type wr_cfl = cl_info option (*write-read conflict*)
type ww_cfl = cl_info option (*write-write conflict*)
type var_info = cl * var
type readSet = var_info option * var_info option
type writeSet = var_info option * var_info option
type cls = TMI | TI | M | E | S | I | N_E (* Non-exist state *)

type state = status * flag * in_com * eps * readSet * writeSet * rw_cfl * wr_cfl * ww_cfl * cls
type statePair = state * state

let status_to_string = function | Active -> "active" | Aborted -> "aborted" | Committed -> "committed" |Invalid -> "invalid" | Non_exist -> "non_exist"
let cfl_to_string = function | None -> "n" | Some (T1, CL1) -> "(t1, cl1)" | Some (T2, CL1) -> "(t2, cl1)"
let var_info_to_string = function | None -> "n" | Some (CL1, V1) -> "(cl1, v1)" | Some (CL1, V2) -> "(cl1, v2)"
let thread_to_string = function | None -> "n" | Some T1 -> "t1" | Some T2 -> "t2"
let flag_to_string = string_of_int
let in_com_to_string = string_of_int
let eps_to_string = string_of_int
let print_wrSet (vi1, vi2) = "(" ^ var_info_to_string vi1 ^ ", " ^ var_info_to_string vi2 ^ ")"
let print_rw_cfl cfl = " rw(" ^ cfl_to_string cfl ^ ")"
let print_wr_cfl cfl = " wr(" ^ cfl_to_string cfl ^ ")"
let print_ww_cfl cfl = " ww(" ^ cfl_to_string cfl ^ ")"
let cls_to_string = function | TMI -> "tmi" | TI -> "ti" | M -> "m" | E -> "e" | S -> "s" | I -> "i" | N_E -> "n-e"
let print_cls cls = "(" ^ cls_to_string cls ^ ") "
let inv_var_info_to_string = function | (CL1, V1) -> "(cl1, v1)" | (CL1, V2) -> "(cl1, v2)"

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
  let cls_s= print_cls cls in
  sta_s^flag_s^in_com_s^eps_s^rs_s^ws_s^rw_cfl_s^wr_cfl_s^ww_cfl_s^cls_s
end

let print_state_pair state1 state2 = begin
  let s1 = print_state state1 in
  let s2 = print_state state2 in
  s1^s2
end

let var_in_set (vi: var_info)  wr_set = begin
  match vi, wr_set with
  | (CL1, V1), (Some(CL1, _), _) -> true
  | (CL1, V2), (_, Some(CL1, _)) -> true
  | _, _ -> false
end

let cl_in_set (vi: var_info) wr_set = begin
  match vi, wr_set with
  | (CL1, _), (Some(CL1, _), _) -> true
  | (CL1, _), (_, Some(CL1, _)) -> true
  | _, _ -> false
end

let add_vi (vi: var_info) wr_set = begin
  match var_in_set vi wr_set with
  | true -> wr_set
  | _ -> begin
      match vi with
      | (CL1, V1) -> (Some (CL1, V1), snd(wr_set))
      |	(CL1, V2)  -> (fst(wr_set), Some (CL1, V2))
  end
end

let cl_in_cfl (ci: cl_info) cfl = begin
  match cfl with
  | Some c_info when ci = c_info -> true
  | _ -> false
end

let add_ci (ci: cl_info) cfl = begin
  match cl_in_cfl ci cfl with
  | true -> cfl
  | _ ->Some ci
end

let if_inter wr_set1 wr_set2 = begin
  match wr_set1, wr_set2 with
  | (Some (CL1, V1), _), (Some (CL1, V1), _) -> true
  | (_, Some (CL1, V2)), (_, Some (CL1, V2)) -> true
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
  | (sta, _, _,  _, _, _, _, _, _, _) -> sta
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

let init_state_pair = ((Committed, 0, 0, 0,  (None, None), (None, None), None, None, None, I), (Committed, 0, 0, 0, (None, None), (None, None), None, None, None, I))
let non_exist = ((Non_exist, 0, 0, 0,  (None, None), (None, None), None, None, None, I), (Non_exist, 0, 0, 0, (None, None), (None, None), None, None, None, I))

let str_init = print_state_pair (fst(init_state_pair)) (snd(init_state_pair))
let p_init = polish_state "" str_init;;
let t_file = "TMESI_Transitions_test.ml"
let f_file = "TMESI_Final_states_test.ml"
let s_file = "TMESI_States_test.ml"
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

let state_no = ref 0

let print_states_to_file hkey = begin
  if (check_status hkey 1) == Non_exist then ()
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

print_states_to_file init_state_pair;;

(* No need to check the status of the other thread, because if there is conflict, then the other thread must be in active status *)
(* otherwise the other thread wouldn't have its ws or rs be non-empty without starting a transaction *)

(* All the reads should be intepreted as global reads because the conflict tables are at cache line granularity. E.g., after a write on a cache line, a read on it might be *)
(* the read on the variable which hasn't been written. In this way, it is a global read. Even though it reads the written variable, other variables that are not written *)
(* are globally read when the cache line is read. If all the variables in the cache line are written, then it can also be put into the read sig because if there is r-w conflict *)
(* with another tx, there must be w-w conflict with that tx. The current tx will be aborted anyway if it is aborted because of the r-w conflict with the remote tx *)

(* According to the TMESI paper, an aborted tx can also start a new tx *)

(*** TODO: test the file printing functionalities ***)
(*** TODO: test the cache line states switching ***)
(*** TODO: make sure there is abort after each state except for the aborted, committed states and before the invisible read or the n_t operation commit ***)
(*** TODO: compare the abort-related paths with those in the reference automaton and make sure the paths are the same ***)
(*** TODO: make sure that there is no path that ends up with a non-final state ***)
(*** TODO: add the comments to the program ***)

(*No need to check if the status is invalid at the beginning of a transition since all the invalid states are aborted right after the invalidation operation*)
let tread_t1 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  (* when flg is not equal to 0, it means that the tx in being non-tx read/written and not finished yet. All the tx operations should serialize after the non-tx ones *)
  if (((flg1 != 0) || (flg2 != 0)) || (in_com1 != 0)) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls1, cls2 with
      | I, I -> (E, cls2)
      |	I, TMI -> (TI, cls2)
      |	I, TI -> (S, cls2)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	TMI, TMI -> (cls1, cls2)
      |	TMI, TI -> (cls1, cls2)
      |	TMI, I -> (cls1, cls2)
      |	TMI, _ -> (N_E, N_E) (* TMI and M/E/S cannot exist at the same time*)
      |	TI, M -> (N_E, N_E)
      |	TI, E -> (N_E, N_E)
      |	TI, TI -> (N_E, N_E)
      |	TI, _ -> (cls1, cls2) (* TI, TMI/S/I *)
      |	_, I -> (cls1, cls2) (* M/E/S, I *)
      |	S, TI -> (cls1, cls2)
      |	S, S -> (cls1, cls2)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let rs = add_vi vi rs1 in
      let (rw_cfl, wr_cfl) =
	match cl_in_set vi ws2 with
	| true -> ((add_ci (T2, CL1) rw_cfl1), (add_ci (T1, CL1) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    ((sta, flg1, in_com1, eps1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, cls1_f), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, cls2_f))
    end
  end
end

let tread_t2 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls2, cls1 with
      | I, I -> (E, cls1)
      |	I, TMI -> (TI, cls1)
      |	I, TI -> (S, cls1)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	TMI, TMI -> (cls2, cls1)
      |	TMI, TI -> (cls2, cls1)
      |	TMI, I -> (cls2, cls1)
      |	TMI, _ -> (N_E, N_E) (* TMI and M/E/S cannot exist at the same time*)
      |	TI, M -> (N_E, N_E)
      |	TI, E -> (N_E, N_E)
      |	TI, TI -> (N_E, N_E)
      |	TI, _ -> (cls2, cls1) (* TI, TMI/S/I *)
      |	_, I -> (cls2, cls1) (* M/E/S, I *)
      |	S, TI -> (cls2, cls1)
      |	S, S -> (cls2, cls1)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
   in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let rs = add_vi vi rs2 in
      let (rw_cfl, wr_cfl) =
	match cl_in_set vi ws1 with
	| true -> ((add_ci (T1, CL1) rw_cfl2), (add_ci (T2, CL1) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, cls1_f), (sta, flg2, in_com2, eps2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, cls2_f))
    end
  end
end

let twrite_t1 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls1, cls2 with
      | _, I -> (TMI, cls2) (* TMI/TI/M/E/S/I, I *)
      |	I, TMI -> (TMI, cls2)
      |	TI, TMI -> (TMI, cls2)
      |	TMI, TMI -> (cls1, cls2)
      |	_, TMI -> (N_E, N_E) (* M/E/S, TMI *)
      |	S, TI -> (TMI, cls2)
      |	I, TI -> (TMI, cls2)
      |	TMI, TI -> (cls1, cls2)
      |	_, TI -> (N_E, N_E) (* M/E/TI, TI *)
      |	I, _ -> (TMI, I) (* I, M/E/S *)
      |	S, S -> (TMI, I)
      |	TI, S -> (TMI, I)
      |	_, _ -> (N_E, N_E) (* TMI/M/E/S, M/E and TMI/TI/M/E, S *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let ws = add_vi vi ws1 in
      let (wr_cfl, rw_cfl) =
	match cl_in_set vi rs2 with
	| true -> ((add_ci (T2, CL1) wr_cfl1), (add_ci (T1, CL1) rw_cfl2))
	| _ -> (wr_cfl1, rw_cfl2)
      in
      let (ww_cfl1_f, ww_cfl2_f) =
	match cl_in_set vi ws2 with
	| true -> ((add_ci (T2, CL1) ww_cfl1), (add_ci (T1, CL1) ww_cfl2))
	| _ -> (ww_cfl1, ww_cfl2)
      in
    ((sta, flg1, in_com1, eps1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, cls1_f), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, cls2_f))
    end
  end
end

let twrite_t2 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((flg1 != 0) || (flg2 != 0)) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls2, cls1 with
      | _, I -> (TMI, cls1) (* TMI/TI/M/E/S/I, I *)
      |	I, TMI -> (TMI, cls1)
      |	TI, TMI -> (TMI, cls1)
      |	TMI, TMI -> (cls2, cls1)
      |	_, TMI -> (N_E, N_E) (* M/E/S, TMI *)
      |	S, TI -> (TMI, cls1)
      |	I, TI -> (TMI, cls1)
      |	TMI, TI -> (cls2, cls1)
      |	_, TI -> (N_E, N_E) (* M/E/TI, TI *)
      |	I, _ -> (TMI, I) (* I, M/E/S *)
      |	S, S -> (TMI, I)
      |	TI, S -> (TMI, I)
      |	_, _ -> (N_E, N_E) (* TMI/TI/M/E/S, M/E and TMI/TI/M/E, S *)
    in
    if (cls2_f, cls1_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let ws = add_vi vi ws2 in
      let (wr_cfl, rw_cfl) =
	match cl_in_set vi rs1 with
	| true -> ((add_ci (T1, CL1) wr_cfl2), (add_ci (T2, CL1) rw_cfl1))
	| _ -> (wr_cfl2, rw_cfl1)
      in
      let (ww_cfl1_f, ww_cfl2_f) =
	match cl_in_set vi ws1 with
	| true -> ((add_ci (T2, CL1) ww_cfl1), (add_ci (T1, CL1) ww_cfl2))
	| _ -> (ww_cfl1, ww_cfl2)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, cls1_f), (sta, flg2, in_com2, eps2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, cls2_f))
    end
  end
end

let abort_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta1 = Aborted || sta1 = Committed) || flg1 != 0) || flg2 != 0) (* || in_com1 != 0) *)  then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls1, cls2 with
      | TMI, TMI -> (I, cls2)
      | TMI, TI -> (I, cls2)
      | TMI, I -> (I, cls2)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls2)
      |	TI, S -> (I, cls2)
      |	TI, I -> (I, cls2)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls1, cls2) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx aborts, the I cache line state doesn't change *)
      |	_, I -> (cls1, cls2) (* M/E/S, I *)
      |	S, S -> (cls1, cls2)
      |	S, TI -> (cls1, cls2)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Aborted in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = None in
      let wr_cfl = None in
      let ww_cfl = None in
      let in_com2_f = in_com2 + 1 in
      let output =((sta, flg1, 0, 0, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, in_com2_f, 0, rs2, ws2, rw_cfl, wr_cfl, ww_cfl, cls2_f)) in
      print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "abtt1";
      output
    end
  end
end

let abort_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta2 = Aborted || sta2 = Committed) || flg1 != 0) || flg2 != 0) (* || in_com2 != 0) *) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls2, cls1 with
      | TMI, TMI -> (I, cls1)
      | TMI, TI -> (I, cls1)
      | TMI, I -> (I, cls1)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls1)
      |	TI, S -> (I, cls1)
      |	TI, I -> (I, cls1)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls2, cls1) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx aborts, the I cache line state doesn't change *)
      |	_, I -> (cls2, cls1) (* M/E/S, I *)
      |	S, S -> (cls2, cls1)
      |	S, TI -> (cls2, cls1)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/TI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Aborted in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = None in
      let wr_cfl = None in
      let ww_cfl = None in
      let in_com1_f = in_com1 + 1 in
      let output = ((sta1, flg1, in_com1_f, 0, rs1, ws1, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta, flg2, 0, 0, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)) in
      print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "abtt2";
      output
    end
  end
end

let commit_one_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  let eps = 1 in
  
  if ((((sta1 = Aborted || sta1 = Committed) || flg1 != 0) || flg2 != 0) || in_com1 != 0) then non_exist
  else begin
    if (in_com2 != 0) then begin
      let in_com1_f = in_com1 + 1 in
      let in_com2_f = in_com2 + 1 in
      let output = ((sta1, flg1, in_com1_f, eps, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in
      Eps_trans.add eps_trans (output, "com_one, t1") ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2));
      (* let print output = begin *)
      (* match (var_in_set (CL1, V1) rs1), (var_in_set (CL1, V2) rs1), (var_in_set (CL1, V1) ws1), (var_in_set (CL1, V2) ws1) with *)
      (* |	true, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt1v1" *)
      (* |	_, true, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt1v2" *)
      (* |	_, _, true, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt1v1" *)
      (* |	_, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt1v2" *)
      (* end in *)
      (* print output; *)
      output
    end
	
    else begin
      let if_abort = begin
      	match wr_cfl1, rw_cfl2, ww_cfl1, ww_cfl2 with
        | Some (T2, _), Some (T1, _), _, _ -> true (* the other tx should be aborted only when the cfl in both threads are unempty, because sometimes the neighbour can be aborted or committed *)
      	| _, _, Some (T2, _), Some (T1, _) -> true
      	| _, _, _, _ -> false
      end in
      
      (*** in_com1 should be increased by 1 even if there are conflicts, since it ensures that t1 is in commit and cannot do any read or write instructions ***)
      
      let in_com1_f = in_com1 + 1 in
      let output_abt = ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in
      let output_eps = ((sta1, flg1, in_com1_f, eps, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in
      
      match if_abort with (*** TODO: print_states_to_file of the one applied to abort_t2 ***)
      |	true -> begin
	  print_states_to_file output_abt;
	  abort_t2 (fst(output_abt)) (snd(output_abt))
      end
      |	_ -> begin
	  Eps_trans.add eps_trans (output_eps, "com_one, t1") ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2));
	  (* let print output = begin *)
	  (*       match (var_in_set (CL1, V1) rs1), (var_in_set (CL1, V2) rs1), (var_in_set (CL1, V1) ws1), (var_in_set (CL1, V2) ws1) with *)
	  (* 	| true, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt1v1" *)
	  (* 	| _, true, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt1v2" *)
	  (* 	| _, _, true, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt1v1" *)
	  (* 	| _, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt1v2" *)
          (* end in *)
	  (* print output; *)
	  output_eps
      end
    end
  end
end

let commit_one_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  let eps = 1 in
  
  if ((((sta2 = Aborted || sta2 = Committed) || flg1 != 0) || flg2 != 0) || in_com2 != 0) then non_exist
  else begin
    if (in_com1 != 0) then begin
      let in_com1_f = in_com1 + 1 in
      let in_com2_f = in_com2 + 1 in
      let output = ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2_f, eps, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in
      Eps_trans.add eps_trans (output, "com_one, t2") ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2));
      (* let print output = begin *)
      (* match (var_in_set (CL1, V1) rs2), (var_in_set (CL1, V2) rs2), (var_in_set (CL1, V1) ws2), (var_in_set (CL1, V2) ws2) with *)
      (* |	true, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt2v1" *)
      (* |	_, true, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt2v2" *)
      (* |	_, _, true, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt2v1" *)
      (* |	_, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt2v2" *)
      (* end in *)
      (* print output; *)
      output
    end
    
    else begin
      let if_abort = begin
	match wr_cfl2, rw_cfl1, ww_cfl2, ww_cfl1 with
	| Some (T1, _), Some (T2, _), _, _ -> true
	| _, _, Some (T1, _), Some (T2, _) -> true
	| _, _, _, _ -> false
      end in
      
      let in_com2_f = in_com2 + 1 in
      let output_abt = ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in
      let output_eps = ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2_f, eps, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in
      
      match if_abort with
      | true -> begin
	  print_states_to_file output_abt;
	  abort_t1 (fst(output_abt)) (snd(output_abt))
      end
      | _ -> begin
	  Eps_trans.add eps_trans (output_eps, "com_one, t2") ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2));
	  (* let print output = begin *)
	  (*   match (var_in_set (CL1, V1) rs2), (var_in_set (CL1, V2) rs2), (var_in_set (CL1, V1) ws2), (var_in_set (CL1, V2) ws2) with *)
	  (*   | true, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt2v1" *)
	  (*   | _, true, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt2v2" *)
	  (*   | _, _, true, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt2v1" *)
	  (*   | _, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt2v2" *)
          (* end in *)
	  (* print output; *)
	  output_eps
      end
    end
  end
end

let commit_two_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  let eps = 0 in
  
  if (((((sta1 = Aborted || sta1 = Committed) || flg1 != 0) || flg2 != 0) || in_com1 = 0) || in_com1 < in_com2) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls1, cls2 with
      | TMI, TMI -> (M, I)
      | TMI, TI -> (M, I)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls2)
      |	TI, S -> (I, cls2)
      |	TI, I -> (I, cls2)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls1, cls2) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls1, cls2) (* M/E/S, I *)
      |	S, S -> (cls1, cls2)
      |	S, TI -> (cls1, cls2)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let if_abort = begin
      	match wr_cfl1, rw_cfl2, ww_cfl1, ww_cfl2 with
        | Some (T2, _), Some (T1, _), _, _ -> true (* the other tx should be aborted only when the cfl in both threads are unempty, because sometimes the neighbour can be aborted or committed *)
      	| _, _, Some (T2, _), Some (T1, _) -> true
      	| _, _, _, _ -> false
      end in
      
      let in_com1_f = 0 in
      let in_com2_f = 0 in
      let output = ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in
      
      if (if_abort = true) then begin
	(* let print output = begin *)
	(*   match (var_in_set (CL1, V1) rs1), (var_in_set (CL1, V2) rs1), (var_in_set (CL1, V1) ws1), (var_in_set (CL1, V2) ws1) with *)
	(*     | true, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt1v1"; *)
	(* 	print_states_to_file output *)
	(*     | _, true, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt1v2"; *)
	(* 	print_states_to_file output *)
	(*     | _, _, true, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt1v1"; *)
	(* 	print_states_to_file output *)
	(*     | _, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt1v2"; *)
	(* 	print_states_to_file output *)
	(* end in *)
	(* print output;  *)
	let output_abt = commit_one_t1 (fst(output)) (snd(output)) in
	if output_abt = non_exist then printf "The output_abt of %s\n is non_exist: \n" (print_state_pair (fst(output)) (snd(output)));
	if eps2 != 0 then output_abt else begin
	  print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output_abt "abtt2";
	  output_abt
	end
      end
      
      else begin
	let sta = Committed in
	let rs = (None, None) in
	let ws = (None, None) in
	let rw_cfl = None in
	let wr_cfl = None in
	let ww_cfl = None in
	
	let empty_rw = begin
	  match rw_cfl1 with
	  | Some (T2, _) -> true
	  | _ -> false
	end in
	
	let output_com = begin
	  match empty_rw with
	  | true -> ((sta, flg1, in_com1_f, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, None, ww_cfl2, cls2_f))
	  | false -> ((sta, flg1, in_com1_f, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, in_com2_f, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2_f)) end in
	if eps2 != 0 then output_com else begin
	  print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output_com "comt1";
	  output_com
	end
      end
    end
  end
end

(* let test_st1 = ((Active, 0, 0, 0,  (None, Some (CL1, V2)), (Some (CL1, V1), None), None, Some (T2, CL1), None, TMI), (Active, 0, 0, 0, (Some (CL1, V1), Some (CL1, V2)), (None, None), Some (T1, CL1), None, None, TI));; *)
(* let test_st2 = *)
(*   ((Active, 0, 0, 0, (None, Some V2), (None, None), (None, None), (None, None), (None, None), (I, E)), (Committed, 0, 0, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)));; *)

(* let com_one_t1_st = commit_one_t1 (fst(test_st1)) (snd(test_st1));; *)
(* let com_two_t1_st = commit_two_t1 (fst(com_one_t1_st)) (snd(com_one_t1_st));; *)
(* let abort_t2_st = abort_t2 (fst(test_st1)) (snd(test_st1));; *)
(* let com_one_t1_str = print_state_pair (fst(com_one_t1_st)) (snd(com_one_t1_st));; *)
(* let com_two_t1_str = print_state_pair (fst(com_two_t1_st)) (snd(com_two_t1_st));; *)
(* let abort_t2_str = print_state_pair (fst(abort_t2_st)) (snd(abort_t2_st));; *)
(* printf "The result of commit_one_t1 of the state is:\n %s\n" com_one_t1_str;; *)
(* printf "The result of abort_t2 of the state is:\n %s\n" abort_t2_str;; *)

let commit_two_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  let eps = 0 in
  if (((((sta2 = Aborted || sta2 = Committed) || flg1 != 0) || flg2 != 0) || in_com2 = 0) || in_com2 < in_com1) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls2, cls1 with
      | TMI, TMI -> (M, I)
      | TMI, TI -> (M, I)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, M/E/S *)
      |	TI, TMI -> (I, cls1)
      |	TI, S -> (I, cls1)
      |	TI, I -> (I, cls1)
      |	TI, _ -> (N_E, N_E) (* TI, TI/M/E *)
      |	I, _ -> (cls2, cls1) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls2, cls1) (* M/E/S, I *)
      |	S, S -> (cls2, cls1)
      |	S, TI -> (cls2, cls1)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/TI/M/E *)
    in
    if (cls2_f, cls1_f) = (N_E, N_E) then non_exist
    
    else begin
      let if_abort = begin
      	match wr_cfl2, rw_cfl1, ww_cfl2, ww_cfl1 with
        | Some (T1, _), Some (T2, _), _, _ -> true
      	| _, _, Some (T1, _), Some (T2, _) -> true
      	| _, _, _, _ -> false
      end in
      
      let in_com1_f = 0 in
      let in_com2_f = 0 in
      let output = ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2_f, eps, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in
      
      if (if_abort = true) then begin
	(* let print output = begin *)
	(*   match (var_in_set (CL1, V1) rs2), (var_in_set (CL1, V2) rs2), (var_in_set (CL1, V1) ws2), (var_in_set (CL1, V2) ws2) with *)
	(*     | true, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt2v1"; *)
	(* 	print_states_to_file output *)
	(*     | _, true, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "rdt2v2"; *)
	(* 	print_states_to_file output *)
	(*     | _, _, true, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt2v1"; *)
	(* 	print_states_to_file output *)
	(*     | _, _, _, _ -> print_to_files (sta1, flg1, in_com1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output "wrt2v2"; *)
	(* 	print_states_to_file output *)
	(* end in *)
	(* print output;  *)
	let output_abt = commit_one_t2 (fst(output)) (snd(output)) in
	if eps1 != 0 then output_abt else begin
	  print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output_abt "abtt1";
	  output_abt
	end
      end
      
      else begin
	let sta = Committed in
	let rs = (None, None) in
	let ws = (None, None) in
	let rw_cfl = None in
	let wr_cfl = None in
	let ww_cfl = None in
	
	let empty_rw = begin
	  match rw_cfl2 with
	  | Some (T1, _) -> true
	  | _ -> false
	end in
	
	let output_com = begin
	  match empty_rw with
	  | true -> ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, None, ww_cfl1, cls1_f), (sta, flg2, in_com2_f, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f))
	  | false -> ((sta1, flg1, in_com1_f, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1_f), (sta, flg2, in_com2_f, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)) end in
	if eps1 != 0 then output_com else begin
	  print_to_files (sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2) output_com "comt2";
	  output_com
	end
      end
    end
  end
end

let nread_t1 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta1 == Active || flg1 != 0) || flg2 != 0) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls1, cls2 with
      |	M, I -> (cls1, cls2)
      |	E, I -> (cls1, cls2)
      |	S, I -> (cls1, cls2)
      |	S, S -> (cls1, cls2)
      |	S, TI -> (cls1, cls2)
      |	I, TMI -> (cls1, cls2)
      |	I, TI -> (S, TI)
      |	I, I -> (E, I)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta = Active in
      let flg1_f = 1 in
      let rs = add_vi vi rs1 in
      let (rw_cfl, wr_cfl) =
	match cl_in_set vi ws2 with
	| true -> ((add_ci (T2, CL1) rw_cfl1), (add_ci (T1, CL1) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    ((sta, flg1_f, in_com1, eps1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, cls1_f), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, cls2_f))
    end
  end
end

let nread_t2 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta2 == Active || flg1 != 0) || flg2 != 0) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls2, cls1 with
      |	M, I -> (cls2, cls1)
      |	E, I -> (cls2, cls1)
      |	S, I -> (cls2, cls1)
      |	S, S -> (cls2, cls1)
      |	S, TI -> (cls2, cls1)
      |	I, TMI -> (cls2, cls1)
      |	I, TI -> (S, TI)
      |	I, I -> (E, I)
      |	I, _ -> (S, S) (* I, M/E/S *)
      |	_, _ -> (N_E, N_E) (* TMI/TI, TMI/TI/M/E/S/I and M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if (cls1_f, cls2_f) = (N_E, N_E) then non_exist
    else begin
      let sta =  Active in
      let flg2_f = 1 in
      let rs = add_vi vi rs2 in
      let (rw_cfl, wr_cfl) =
	match cl_in_set vi ws1 with
	| true -> (* let wr_cfl1_f = (add_ci (T2, CL1) wr_cfl1) in *)
	    (* let rw_cfl2_f = (add_ci (T1, CL1) rw_cfl2) in *)
	    (* printf "So now wr_cfl1 and rw_cfl2 are: %s, %s\n" (cfl_to_string wr_cfl1_f) (cfl_to_string rw_cfl2_f); *)
	    ((add_ci (T1, CL1) rw_cfl2), (add_ci (T2, CL1) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, cls1_f), (sta, flg2_f, in_com2, eps2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, cls2_f))
    end
  end
end

let nwrite_t1 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta1 == Active || flg1 != 0) || flg2 != 0) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls1, cls2 with
      |	M, I -> (cls1, cls2)
      |	E, I -> (M, cls2)
      |	S, I -> (M, cls2)
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
      let ws = add_vi vi ws1 in
      let ((wr_cfl, rw_cfl), flg2_f') =
	match cl_in_set vi rs2 with
	| true -> (((add_ci (T2, CL1) wr_cfl1), (add_ci (T1, CL1) rw_cfl2)), 2)
	| _ -> ((wr_cfl1, rw_cfl2), flg2)
      in
      let ((ww_cfl1_f, ww_cfl2_f), flg2_f) =
	match cl_in_set vi ws2 with
	| true -> (((add_ci (T2, CL1) ww_cfl1), (add_ci (T1, CL1) ww_cfl2)), 2)
	| _ -> ((ww_cfl1, ww_cfl2), flg2_f')
      in
    ((sta, flg1_f, in_com1, eps1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, cls1_f), (sta2, flg2_f, in_com2, eps2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, cls2_f))
    end
  end
end

let nwrite_t2 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta2 == Active || flg1 != 0) || flg2 != 0) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls2, cls1 with
      |	M, I -> (cls2, cls1)
      |	E, I -> (M, cls1)
      |	S, I -> (M, cls1)
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
      let ws = add_vi vi ws2 in
      let ((wr_cfl, rw_cfl), flg1_f') =
	match cl_in_set vi rs1 with
	| true -> (((add_ci (T1, CL1) wr_cfl2), (add_ci (T2, CL1) rw_cfl1)), 2)
	| _ -> ((wr_cfl2, rw_cfl1), flg1)
      in
      let ((ww_cfl2_f, ww_cfl1_f), flg1_f) =
	match cl_in_set vi ws1 with
	| true -> (((add_ci (T2, CL1) ww_cfl2), (add_ci (T1, CL1) ww_cfl1)), 2)
	| _ -> ((ww_cfl2, ww_cfl1), flg1_f')
      in
    ((sta1, flg1_f, in_com1, eps1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, cls1_f), (sta, flg2_f, in_com2, eps2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, cls2_f))
    end
  end
end

let nabort_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta1 != Invalid || flg1 != 2) || flg2 != 1) || in_com2 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls1, cls2 with
      | TMI, TMI -> (I, cls2)
      | TMI, I -> (I, cls2)
      |	_, _ -> (cls1, cls2)
    in
(* when a tx needs to be aborted, the conflicts can be (in the order of tx and non-tx) w-w (TMI, TMI), r-w (_, _) (because TI would have been I when nwrite, and a pure tx-read in a tx *)
(* doesn't have T-stats so the nabort won't change the states of the tx) and w-r (TMI, I) (the non-tx stays in I if the tx has TMI). In this way, only TMI, TMI and TMI, I these two cases *)
(* need to be illustrated in nabort *)
    
    let sta = Aborted in
    let flg = 0 in
    let rs = (None, None) in
    let ws = (None, None) in
    let rw_cfl = None in
    let wr_cfl = None in
    let ww_cfl = None in
    ((sta, flg, 0, eps1, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, 0, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2_f))
  end
end

let nabort_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta2 != Invalid || flg2 != 2) || flg1 != 1) || in_com1 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls2, cls1 with
      | TMI, TMI -> (I, cls1)
      | TMI, I -> (I, cls1)
      |	_, _ -> (cls2, cls1)
    in
    
    let sta = Aborted in
    let flg = 0 in
    let rs = (None, None) in
    let ws = (None, None) in
    let rw_cfl = None in
    let wr_cfl = None in
    let ww_cfl = None in
    ((sta1, flg1, 0, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1_f), (sta, flg, 0, eps2, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f))
  end
end

let ncommit_t1 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta1 != Active || flg1 != 1) || in_com1 != 0) then non_exist
  else begin
    let (cls1_f, cls2_f) =
      match cls1, cls2 with
      | TMI, TMI -> (M, I)
      |	_, _ -> (cls1, cls2) (* there is only one case that the cache line state should be changed after a non-tx read/write. All the other cases keep the cache line states unchaged *)
    in
    
    let flg = 0 in
    let sta = Committed in
    let rs = (None, None) in
    let ws = (None, None) in
    let rw_cfl = None in
    let wr_cfl = None in
    let ww_cfl = None in
      
    (* let naborted_part = snd (nabort_t2 (sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in *)
    let abt_cls2 = fst(naborted_cls cls2 cls1) in
    let invalid_state = (Invalid, 0, 0, eps2, (None, None), (None, None), None, None, None, abt_cls2) in
    if flg2 = 2 then ((sta, flg, 0, eps1, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), invalid_state)
    else ((sta, flg, 0, eps1, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2_f))
  end
end

let ncommit_t2 ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta2 != Active || flg2 != 1) || in_com2 != 0) then non_exist
  else begin
    let (cls2_f, cls1_f) =
      match cls2, cls1 with
      | TMI, TMI -> (M, I)
      |	_, _ -> (cls2, cls1) (* there is only one case that the cache line state should be changed after a non-tx read/write. All the other cases keep the cache line states unchaged *)
    in
    
    let flg = 0 in
    let sta = Committed in
    let rs = (None, None) in
    let ws = (None, None) in
    let rw_cfl = None in
    let wr_cfl = None in
    let ww_cfl = None in
      
    (* let naborted_part = fst (nabort_t1 (sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in *)
    let abt_cls1 = fst(naborted_cls cls1 cls2) in
    let invalid_state = (Invalid, 0, 0, eps1, (None, None), (None, None), None, None, None, abt_cls1) in
    if flg1 = 2 then (invalid_state, (sta, flg, 0, eps2, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f))
    else ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1_f), (sta, flg, 0, eps2, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f))
  end
end

(* The invisible_read functions are actually the same as tx_read/nt_read functions. The only difference is that some information such as cache line state doesn't need to be checked. Only the rs needs *)
(* to be updated. So it takes shorter time to invoke an inv_read function than a normal read function. Meanwhile, an inv_read function can also be regarded as a normal read funcion in the automaton *)

let inv_read_t1 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  let rs = add_vi vi rs1 in
  ((sta1, flg1, in_com1, eps1, rs, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2))
end

let inv_read_t2 (vi: var_info) ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  let rs = add_vi vi rs2 in
  ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, eps2, rs, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2))
end

let get_flg state = begin
  match state with
  | (_, flg, _,  _, _, _, _, _, _, _) -> flg
end

let get_in_com state = begin
  match state with
  | (_, _, in_com, _, _, _, _, _, _, _) -> in_com
end

let get_eps state = begin
  match state with
  | (_, _, _, eps, _, _, _, _, _, _) -> eps
end

let zero_eps ((sta1, flg1, in_com1, eps1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, in_com2, eps2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  ((sta1, flg1, in_com1, 0, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, in_com2, 0, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2))
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

let inv_to_abt (sta, flg, in_com, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls) = begin
  let sta_f = Aborted in
  (sta_f, flg, in_com, eps, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls)
end

let ref_loop = ref 0


(********** THE BEGINNING OF THE TESTING CODING **********)

(*** TODO: test all the transition fuctions ***)
(*** TODO: test all the cache line state switching ***)

(*** TODO: test the post states of the initial state, add the printing functionality first and test the rest of the functionalities ***)
(* let state1 = (Active, 0, 0, (Some (CL1, V1), Some (CL1, V2)), (None, None), (Some (T2, CL1)), None, None, TI) *)
(* let state2 = (Active, 0, 1, (Some (CL1, V1), Some (CL1, V2)), (None, None), None, (Some (T1, CL1)), None, TMI) *)
(* let post_state = commit_two_t2 state1 state2 *)
(* let final_state = nabort_t2 (fst(com_state)) (snd(com_state)) *)

(* let post_str = print_state_pair (fst(post_state)) (snd(post_state));; *)
(* let com_str = print_state_pair (fst(com_state)) (snd(com_state));; *)
(* let final_str = print_state_pair (fst(final_state)) (snd(final_state));; *)
(* printf "The post state pair is:\n%s\n" post_str;; *)
(* printf "The commit state pair is:\n%s" com_str;; *)
(* printf "The final state pair is:\n%s" final_str;; *)

(* let final = get_post_state (fst(init_state_pair)) (snd(init_state_pair));; *)
(* let final = get_post_state state1 state2;; *)
(* printf "\nThe post states of the initial state are:\n";; *)
(* List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) final;; *)

(* The post states of active0(n, some (cl1, v2))(some (cl1, v1), n) rw(n) wr(n) ww(n)(tmi) active1(some (cl1, v1), some (cl1, v2))(n, n) rw(n) wr(n) ww(n)(i)  are: *)
(* active0(n, some (cl1, v2))(some (cl1, v1), n) rw(n) wr(n) ww(n)(tmi) committed0(n, n)(n, n) rw(n) wr(n) ww(n)(i)  *)
(* active0(n, some (cl1, v2))(some (cl1, v1), n) rw(n) wr(n) ww(n)(tmi) committed0(n, n)(n, n) rw(n) wr(n) ww(n)(i) *)

(********** THE END OF THE TESTING CODING **********)


(* Each read/write actually includes an invisible read. So the hash table records both the read/write operation and the invisible read operation. The output of the get_post_state function is the list *)
(* of the states after both read/write and invisible read. E.g., When after_tread_t1_v1 state S, A_S is after tread_t1_v1 S and then invisibly tread_t1_v2 S. So A_S will be in the list of the output. *)
(* But both post states of (tread_t1_v1 S) and (tread_t1_v2 S) are counted into the number of the states of the TMESI *)

(* only invoking print_states_to_file in the non-final states, then adding the final states in from the visted list like the reference automaton is not correct here. Because an after_trd_t1_v1 *)
(* final state will not change when a trd_t1_v1 applies on it. This is not a final state but is the same as a final one, so it will be printed out in the TMESI_States.ml. While the same state which *)
(* appears in the visisted list will also be printed out, without invoking print_states_to_file because all the visited list is simply copied into the file. A secure way is to invoke print_states_to_file *)
(* whenever there can be a new state generated in get_post_state. The duplicated states will filtered out by print_states_to_file *)
let get_post_state state1 state2 = begin
  (* The single tx read operation. I.e., without the invisible read operation *)
  let trd_t1_v1 =
    try
      Forward.find forward ((state1, state2), "tx, rd, t1, v1, cl1")
    with Not_found ->
      let post_state = tread_t1 (CL1, V1) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt1v1";
  	      Forward.add forward ((state1, state2), "tx, rd, t1, v1, cl1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
	  | (_, 0) -> get_pre_t1 state1 state2 post_state "rdt1v1" "tx, rd, t1, v1, cl1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "rdt1v1" "tx, rd, t1, v1, cl1"
	  | (_, _) -> get_pre_both state1 state2 post_state "rdt1v1" "tx, rd, t1, v1, cl1"
      end
  in
  	  (* printf "No. %d: trd_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(trd_t1_v1)) (snd(trd_t1_v1))); *)

  let trd_t1_v2 =
    try
      Forward.find forward ((state1, state2), "tx, rd, t1, v2, cl1")
    with Not_found ->
      let post_state = tread_t1 (CL1, V2) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt1v2";
  	      Forward.add forward ((state1, state2), "tx, rd, t1, v2, cl1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
	  | (_, 0) -> get_pre_t1 state1 state2 post_state "rdt1v2" "tx, rd, t1, v2, cl1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "rdt1v2" "tx, rd, t1, v2, cl1"
	  | (_, _) -> get_pre_both state1 state2 post_state "rdt1v2" "tx, rd, t1, v2, cl1"
      end
  in
 	  (* printf "No. %d: trd_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(trd_t1_v2)) (snd(trd_t1_v2))); *)

  (* The real after_tread_t1_v1 is trd_t1_v1 plus invisible trd_t1_v2 *)
  let after_tread_t1_v1 =
    if (check_status trd_t1_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(trd_t1_v1) in
      let st2 = snd(trd_t1_v1) in
      try
  	Forward.find forward ((st1, st2), "inv, rd, t1, v2, cl1")
      with Not_found ->
  	let post_state = inv_read_t1 (CL1, V2) st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "rdt1v2";
  	    Forward.add forward ((st1, st2), "inv, rd, t1, v2, cl1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_tread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t1_v1)) (snd(after_tread_t1_v1))); *)

  let after_tread_t1_v2 =
    if (check_status trd_t1_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(trd_t1_v2) in
      let st2 = snd(trd_t1_v2) in
      try
  	Forward.find forward ((st1, st2), "inv, rd, t1, v1, cl1")
      with Not_found ->
  	let post_state = inv_read_t1 (CL1, V1) st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "rdt1v1";
  	    Forward.add forward ((st1, st2), "inv, rd, t1, v1, cl1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_tread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t1_v2)) (snd(after_tread_t1_v2))); *)

  let trd_t2_v1 =
    try
      Forward.find forward ((state1, state2), "tx, rd, t2, v1, cl1")
    with Not_found ->
      let post_state = tread_t2 (CL1, V1) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt2v1";
  	      Forward.add forward ((state1, state2), "tx, rd, t2, v1, cl1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
	  | (_, 0) -> get_pre_t1 state1 state2 post_state "rdt2v1" "tx, rd, t2, v1, cl1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "rdt2v1" "tx, rd, t2, v1, cl1"
	  | (_, _) -> get_pre_both state1 state2 post_state "rdt2v1" "tx, rd, t2, v1, cl1"
      end
  in
  	  (* printf "No. %d: trd_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(trd_t2_v1)) (snd(trd_t2_v1))); *)

  let trd_t2_v2 =
    try
      Forward.find forward ((state1, state2), "tx, rd, t2, v2, cl1")
    with Not_found ->
      let post_state = tread_t2 (CL1, V2) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt2v2";
  	      Forward.add forward ((state1, state2), "tx, rd, t2, v2, cl1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
	  | (_, 0) -> get_pre_t1 state1 state2 post_state "rdt2v2" "tx, rd, t2, v2, cl1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "rdt2v2" "tx, rd, t2, v2, cl1"
	  | (_, _) -> get_pre_both state1 state2 post_state "rdt2v2" "tx, rd, t2, v2, cl1"
      end
  in
  	  (* printf "No. %d: trd_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(trd_t2_v2)) (snd(trd_t2_v2))); *)

  let after_tread_t2_v1 =
    if (check_status trd_t2_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(trd_t2_v1) in
      let st2 = snd(trd_t2_v1) in
      try
  	Forward.find forward ((st1, st2), "inv, rd, t2, v2, cl1")
      with Not_found ->
  	let post_state = inv_read_t2 (CL1, V2) st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "rdt2v2";
  	    Forward.add forward ((st1, st2), "inv, rd, t2, v2, cl1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_tread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t2_v1)) (snd(after_tread_t2_v1))); *)

  let after_tread_t2_v2 =
    if (check_status trd_t2_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(trd_t2_v2) in
      let st2 = snd(trd_t2_v2) in
      try
  	Forward.find forward ((st1, st2), "inv, rd, t2, v1, cl1")
      with Not_found ->
  	let post_state = inv_read_t2 (CL1, V1) st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "rdt2v1";
  	    Forward.add forward ((st1, st2), "inv, rd, t2, v1, cl1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_tread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t2_v2)) (snd(after_tread_t2_v2))); *)

  let twr_t1_v1 =
    try
      Forward.find forward ((state1, state2), "tx, wr, t1, v1, cl1")
    with Not_found ->
      let post_state = twrite_t1 (CL1, V1) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt1v1";
  	      Forward.add forward ((state1, state2), "tx, wr, t1, v1, cl1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
	  | (_, 0) -> get_pre_t1 state1 state2 post_state "wrt1v1" "tx, wr, t1, v1, cl1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "wrt1v1" "tx, wr, t1, v1, cl1"
	  | (_, _) -> get_pre_both state1 state2 post_state "wrt1v1" "tx, wr, t1, v1, cl1"
      end
  in
  	  (* printf "No. %d: twr_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(twr_t1_v1)) (snd(twr_t1_v1))); *)

  let twr_t1_v2 =
    try
      Forward.find forward ((state1, state2), "tx, wr, t1, v2, cl1")
    with Not_found ->
      let post_state = twrite_t1 (CL1, V2) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt1v2";
  	      Forward.add forward ((state1, state2), "tx, wr, t1, v2, cl1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
	  | (_, 0) -> get_pre_t1 state1 state2 post_state "wrt1v2" "tx, wr, t1, v2, cl1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "wrt1v2" "tx, wr, t1, v2, cl1"
	  | (_, _) -> get_pre_both state1 state2 post_state "wrt1v2" "tx, wr, t1, v2, cl1"
      end
  in
  	  (* printf "No. %d: twr_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(twr_t1_v2)) (snd(twr_t1_v2))); *)

  let after_twrite_t1_v1 =
    if (check_status twr_t1_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(twr_t1_v1) in
      let st2 = snd(twr_t1_v1) in
      try
  	Forward.find forward ((st1, st2), "inv, rd, t1, v2, cl1")
      with Not_found ->
  	let post_state = inv_read_t1 (CL1, V2) st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "rdt1v2";
  	    Forward.add forward ((st1, st2), "inv, rd, t1, v2, cl1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_twrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t1_v1)) (snd(after_twrite_t1_v1))); *)

  let after_twrite_t1_v2 =
    if (check_status twr_t1_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(twr_t1_v2) in
      let st2 = snd(twr_t1_v2) in
      try
  	Forward.find forward ((st1, st2), "inv, rd, t1, v1, cl1")
      with Not_found ->
  	let post_state = inv_read_t1 (CL1, V1) (fst(twr_t1_v2)) (snd(twr_t1_v2)) in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "rdt1v1";
  	    Forward.add forward ((st1, st2), "inv, rd, t1, v1, cl1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_twrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t1_v2)) (snd(after_twrite_t1_v2)));  *)

  let twr_t2_v1 =
    try
      Forward.find forward ((state1, state2), "tx, wr, t2, v1, cl1")
    with Not_found ->
      let post_state = twrite_t2 (CL1, V1) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt2v1";
  	      Forward.add forward ((state1, state2), "tx, wr, t2, v1, cl1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
	  | (_, 0) -> get_pre_t1 state1 state2 post_state "wrt2v1" "tx, wr, t2, v1, cl1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "wrt2v1" "tx, wr, t2, v1, cl1"
	  | (_, _) -> get_pre_both state1 state2 post_state "wrt2v1" "tx, wr, t2, v1, cl1"
      end
  in
  	  (* printf "No. %d: twr_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(twr_t2_v1)) (snd(twr_t2_v1))); *)

  let twr_t2_v2 =
    try
      Forward.find forward ((state1, state2), "tx, wr, t2, v2, cl1")
    with Not_found ->
      let post_state = twrite_t2 (CL1, V2) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match ((get_eps state1), (get_eps state2)) with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt2v2";
  	      Forward.add forward ((state1, state2), "tx, wr, t2, v2, cl1") post_state;
  	      print_states_to_file post_state;
  	      post_state
          end
	  | (_, 0) -> get_pre_t1 state1 state2 post_state "wrt2v2" "tx, wr, t2, v2, cl1"
	  | (0, _) -> get_pre_t2 state1 state2 post_state "wrt2v2" "tx, wr, t2, v2, cl1"
	  | (_, _) -> get_pre_both state1 state2 post_state "wrt2v2" "tx, wr, t2, v2, cl1"
      end
  in
  	  (* printf "No. %d: twr_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(twr_t2_v2)) (snd(twr_t2_v2))); *)

  let after_twrite_t2_v1 =
    if (check_status twr_t2_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(twr_t2_v1) in
      let st2 = snd(twr_t2_v1) in
      try
  	Forward.find forward ((st1, st2), "inv, rd, t2, v2, cl1")
      with Not_found ->
  	let post_state = inv_read_t2 (CL1, V2) st1 st2 in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "rdt2v2";
  	    Forward.add forward ((st1, st2), "inv, rd, t2, v2, cl1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
    end
  in
  	  (* printf "No. %d: after_twrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t2_v1)) (snd(after_twrite_t2_v1))); *)

  let after_twrite_t2_v2 =
    if (check_status twr_t2_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(twr_t2_v2) in
      let st2 = snd(twr_t2_v2) in
      try
  	Forward.find forward ((st1, st2), "inv, rd, t2, v1, cl1")
      with Not_found ->
  	let post_state = inv_read_t2 (CL1, V1) (fst(twr_t2_v2)) (snd(twr_t2_v2)) in
  	match check_status post_state 1 with
  	| Non_exist -> post_state
  	| _ -> begin
  	    print_to_files st1 st2 post_state "rdt2v1";
  	    Forward.add forward ((st1, st2), "inv, rd, t2, v1, cl1") post_state;
  	    print_states_to_file post_state;
  	    post_state
          end
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
(* 	  print_to_files state1 state2 post_state "abtt1"; *)
(* 	  Forward.add forward ((state1, state2), "tx, abt, t1") post_state; *)
(* 	  print_states_to_file post_state; *)
(* 	  post_state *)
(*         end *)
(*   in *)
(* 	  printf "No. %d: after_abt_t1\n%s\n" (!state_no) (print_state_pair (fst(after_abt_t1)) (snd(after_abt_t1))); *)

(*   let after_abt_t2 = *)
(*     try *)
(*       Forward.find forward ((state1, state2), "tx, abt, t2") *)
(*     with Not_found -> *)
(*       let post_state = abort_t2 state1 state2 in *)
(*       match check_status post_state 1 with *)
(*       |	Non_exist -> post_state *)
(*       |	_ -> begin *)
(* 	  print_to_files state1 state2 post_state "abtt2"; *)
(* 	  Forward.add forward ((state1, state2), "tx, abt, t2") post_state; *)
(* 	  print_states_to_file post_state; *)
(* 	  post_state *)
(*         end *)
(*   in *)
(* 	  printf "No. %d: after_abt_t2\n%s\n" (!state_no) (print_state_pair (fst(after_abt_t2)) (snd(after_abt_t2))); *)

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
	  (* printf "No. %d: after_com_one_t1\n%s\n" (!state_no) (print_state_pair (fst(after_com_one_t1)) (snd(after_com_one_t1))); *)

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
	  (* printf "No. %d: after_com_two_t1\n%s\n" (!state_no) (print_state_pair (fst(after_com_two_t1)) (snd(after_com_two_t1))); *)

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

(* first non-tx read v1/v2 in t1 *)
  let nrd_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v1, cl1")
    with Not_found ->
      let post_state = nread_t1 (CL1, V1) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
  	  | 0 -> begin
	      print_to_files state1 state2 post_state "rdt1v1";
	      Forward.add forward ((state1, state2), "nt, rd, t1, v1, cl1") post_state;
	      print_states_to_file post_state;
	      post_state
          end
  	  | _ -> get_pre_t2 state1 state2 post_state "rdt1v1" "nt, rd, t1, v1, cl1"
      end
  in
	  (* printf "No. %d: nrd_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(nrd_t1_v1)) (snd(nrd_t1_v1))); *)

  let nrd_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v2, cl1")
    with Not_found ->
      let post_state = nread_t1 (CL1, V2) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
  	  | 0 -> begin
	      print_to_files state1 state2 post_state "rdt1v2";
	      Forward.add forward ((state1, state2), "nt, rd, t1, v2, cl1") post_state;
	      print_states_to_file post_state;
	      post_state
          end
  	  | _ -> get_pre_t2 state1 state2 post_state "rdt1v2" "nt, rd, t1, v2, cl1"
      end
  in
	  (* printf "No. %d: nrd_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(nrd_t1_v2)) (snd(nrd_t1_v2))); *)

(* then invisibly read the other variable v1/v2 in the same cache line *)
  let mid_nread_t1_v1 =
    if (check_status nrd_t1_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(nrd_t1_v1) in
      let st2 = snd(nrd_t1_v1) in
      try
	Forward.find forward ((st1, st2), "inv, rd, t1, v2, cl1")
      with Not_found ->
	let post_state = inv_read_t1 (CL1, V2) st1 st2 in
	match check_status post_state 1 with
	| Non_exist -> post_state
	| _ -> begin
	    print_to_files st1 st2 post_state "rdt1v2";
	    Forward.add forward ((st1, st2), "inv, rd, t1, v2, cl1") post_state;
	    print_states_to_file post_state;
	    post_state
          end
     end
  in
	  (* printf "No. %d: mid_nread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(mid_nread_t1_v1)) (snd(mid_nread_t1_v1))); *)

(* at last commit the non-tx read *)
  let after_nread_t1_v1 =
    if (check_status mid_nread_t1_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(mid_nread_t1_v1) in
      let st2 = snd(mid_nread_t1_v1) in
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

  let mid_nread_t1_v2 =
    if (check_status nrd_t1_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(nrd_t1_v2) in
      let st2 = snd(nrd_t1_v2) in
      try
	Forward.find forward ((st1, st2), "inv, rd, t1, v1, cl1")
      with Not_found ->
	let post_state = inv_read_t1 (CL1, V1) st1 st2 in
	match check_status post_state 1 with
	| Non_exist -> post_state
	| _ -> begin
	    print_to_files st1 st2 post_state "rdt1v1";
	    Forward.add forward ((st1, st2), "inv, rd, t1, v1, cl1") post_state;
	    print_states_to_file post_state;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(mid_nread_t1_v2)) (snd(mid_nread_t1_v2))); *)

  let after_nread_t1_v2 =
    if (check_status mid_nread_t1_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(mid_nread_t1_v2) in
      let st2 = snd(mid_nread_t1_v2) in
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
	  (* printf "No. %d: after_nread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t1_v1)) (snd(after_nread_t1_v1))); *)

  let nrd_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v1, cl1")
    with Not_found ->
      let post_state = nread_t2 (CL1, V1) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
	      print_to_files state1 state2 post_state "rdt2v1";
	      Forward.add forward ((state1, state2), "nt, rd, t2, v1, cl1") post_state;
	      print_states_to_file post_state;
	      post_state
          end
  	  | _ -> get_pre_t1 state1 state2 post_state "rdt2v1" "nt, rd, t2, v1, cl2"
      end
  in
	  (* printf "No. %d: nrd_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(nrd_t2_v1)) (snd(nrd_t2_v1))); *)

  let nrd_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v2, cl1")
    with Not_found ->
      let post_state = nread_t2 (CL1, V2) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
	      print_to_files state1 state2 post_state "rdt2v2";
	      Forward.add forward ((state1, state2), "nt, rd, t2, v2, cl1") post_state;
	      print_states_to_file post_state;
	      post_state
          end
  	  | _ -> get_pre_t1 state1 state2 post_state "rdt2v2" "nt, rd, t2, v2, cl2"
      end
  in
	  (* printf "No. %d: nrd_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(nrd_t2_v2)) (snd(nrd_t2_v2))); *)

  let mid_nread_t2_v1 =
    if (check_status nrd_t2_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(nrd_t2_v1) in
      let st2 = snd(nrd_t2_v1) in
      try
	Forward.find forward ((st1, st2), "inv, rd, t2, v2, cl1")
      with Not_found ->
	let post_state = inv_read_t2 (CL1, V2) st1 st2 in
	match check_status post_state 1 with
	| Non_exist -> post_state
	| _ -> begin
	    print_to_files st1 st2 post_state "rdt2v2";
	    Forward.add forward ((st1, st2), "inv, rd, t2, v2, cl1") post_state;
	    print_states_to_file post_state;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(mid_nread_t2_v1)) (snd(mid_nread_t2_v1))); *)

  let after_nread_t2_v1 =
    if (check_status mid_nread_t2_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(mid_nread_t2_v1) in
      let st2 = snd(mid_nread_t2_v1) in
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

  let mid_nread_t2_v2 =
    if (check_status nrd_t2_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(nrd_t2_v2) in
      let st2 = snd(nrd_t2_v2) in
      try
	Forward.find forward ((st1, st2), "inv, rd, t2, v1, cl1")
      with Not_found ->
	let post_state = inv_read_t2 (CL1, V1) st1 st2 in
	match check_status post_state 1 with
	| Non_exist -> post_state
	| _ -> begin
	    print_to_files st1 st2 post_state "rdt2v1";
	    Forward.add forward ((st1, st2), "inv, rd, t2, v1, cl1") post_state;
	    print_states_to_file post_state;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(mid_nread_t2_v2)) (snd(mid_nread_t2_v2))); *)

  let after_nread_t2_v2 =
    if (check_status mid_nread_t2_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(mid_nread_t2_v2) in
      let st2 = snd(mid_nread_t2_v2) in
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
      Forward.find forward ((state1, state2), "nt, wr, t1, v1, cl1")
    with Not_found ->
      let post_state = nwrite_t1 (CL1, V1) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
  	  | 0 -> begin
	      print_to_files state1 state2 post_state "wrt1v1";
	      Forward.add forward ((state1, state2), "nt, wr, t1, v1, cl1") post_state;
	      print_states_to_file post_state;
	      post_state
          end
  	  | _ -> get_pre_t2 state1 state2 post_state "wrt1v1" "nt, wr, t1, v1, cl1"
      end
  in
	  (* printf "No. %d: nwr_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(nwr_t1_v1)) (snd(nwr_t1_v1))); *)

  let nwr_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v2, cl1")
    with Not_found ->
      let post_state = nwrite_t1 (CL1, V2) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state2) with
  	  | 0 -> begin
	      print_to_files state1 state2 post_state "wrt1v2";
	      Forward.add forward ((state1, state2), "nt, wr, t1, v2, cl1") post_state;
	      print_states_to_file post_state;
	      post_state
          end
  	  | _ -> get_pre_t2 state1 state2 post_state "wrt1v2" "nt, wr, t1, v2, cl1"
      end
  in
	  (* printf "No. %d: nwr_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(nwr_t1_v2)) (snd(nwr_t1_v2))); *)

  let mid_nwrite_t1_v1 =
    if (check_status nwr_t1_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(nwr_t1_v1) in
      let st2 = snd(nwr_t1_v1) in
      try
	Forward.find forward ((st1, st2), "inv, rd, t1, v2, cl1")
      with Not_found ->
	let post_state = inv_read_t1 (CL1, V2) st1 st2 in
	match check_status post_state 1 with
	| Non_exist -> post_state
	| _ -> begin
	    print_to_files st1 st2 post_state "rdt1v2";
	    Forward.add forward ((st1, st2), "inv, rd, t1, v2, cl1") post_state;
	    print_states_to_file post_state;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nwrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(mid_nwrite_t1_v1)) (snd(mid_nwrite_t1_v1))); *)

  let after_nwrite_t1_v1 =
    if (check_status mid_nwrite_t1_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(mid_nwrite_t1_v1) in
      let st2 = snd(mid_nwrite_t1_v1) in
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

  let mid_nwrite_t1_v2 =
    if (check_status nwr_t1_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(nwr_t1_v2) in
      let st2 = snd(nwr_t1_v2) in
      try
	Forward.find forward ((st1, st2), "inv, rd, t1, v1, cl1")
      with Not_found ->
	let post_state = inv_read_t1 (CL1, V1) st1 st2 in
	match check_status post_state 1 with
	| Non_exist -> post_state
	| _ -> begin
	    print_to_files st1 st2 post_state "rdt1v1";
	    Forward.add forward ((st1, st2), "inv, rd, t1, v1, cl1") post_state;
	    print_states_to_file post_state;
	    post_state
          end
     end
  in
	  (* printf "No. %d: mid_nwrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(mid_nwrite_t1_v2)) (snd(mid_nwrite_t1_v2))); *)

  let after_nwrite_t1_v2 =
    if (check_status mid_nwrite_t1_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(mid_nwrite_t1_v2) in
      let st2 = snd(mid_nwrite_t1_v2) in
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
      Forward.find forward ((state1, state2), "nt, wr, t2, v1, cl1")
    with Not_found ->
      let post_state = nwrite_t2 (CL1, V1) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
	      print_to_files state1 state2 post_state "wrt2v1";
	      Forward.add forward ((state1, state2), "nt, wr, t2, v1, cl1") post_state;
	      print_states_to_file post_state;
	      post_state
          end
  	  | _ -> get_pre_t1 state1 state2 post_state "wrt2v1" "nt, wr, t2, v1, cl1"
      end
  in
	  (* printf "No. %d: nwr_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(nwr_t2_v1)) (snd(nwr_t2_v1))); *)

  let nwr_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v2, cl1")
    with Not_found ->
      let post_state = nwrite_t2 (CL1, V2) state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match (get_eps state1) with
  	  | 0 -> begin
	      print_to_files state1 state2 post_state "wrt2v2";
	      Forward.add forward ((state1, state2), "nt, wr, t2, v2, cl1") post_state;
	      print_states_to_file post_state;
	      post_state
          end
  	  | _ -> get_pre_t1 state1 state2 post_state "wrt2v2" "nt, wr, t2, v2, cl1"
      end
  in
	  (* printf "No. %d: nwr_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(nwr_t2_v2)) (snd(nwr_t2_v2))); *)

  let mid_nwrite_t2_v1 =
    if (check_status nwr_t2_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(nwr_t2_v1) in
      let st2 = snd(nwr_t2_v1) in
      try
	Forward.find forward ((st1, st2), "inv, rd, t2, v2, cl1")
      with Not_found ->
	let post_state = inv_read_t2 (CL1, V2) st1 st2 in
	match check_status post_state 1 with
	| Non_exist -> post_state
	| _ -> begin
	    print_to_files st1 st2 post_state "rdt2v2";
	    Forward.add forward ((st1, st2), "inv, rd, t2, v2, cl1") post_state;
	    print_states_to_file post_state;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nwrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(mid_nwrite_t2_v1)) (snd(mid_nwrite_t2_v1))); *)

  let after_nwrite_t2_v1 =
    if (check_status mid_nwrite_t2_v1 1) == Non_exist then non_exist
    else begin
      let st1 = fst(mid_nwrite_t2_v1) in
      let st2 = snd(mid_nwrite_t2_v1) in
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

  let mid_nwrite_t2_v2 =
    if (check_status nwr_t2_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(nwr_t2_v2) in
      let st2 = snd(nwr_t2_v2) in
      try
	Forward.find forward ((st1, st2), "inv, rd, t2, v1, cl1")
      with Not_found ->
	let post_state = inv_read_t2 (CL1, V1) st1 st2 in
	match check_status post_state 1 with
	| Non_exist -> post_state
	| _ -> begin
	    print_to_files st1 st2 post_state "rdt2v1";
	    Forward.add forward ((st1, st2), "inv, rd, t2, v1, cl1") post_state;
	    print_states_to_file post_state;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nwrite_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(mid_nwrite_t2_v2)) (snd(mid_nwrite_t2_v2))); *)

  let after_nwrite_t2_v2 =
    if (check_status mid_nwrite_t2_v2 1) == Non_exist then non_exist
    else begin
      let st1 = fst(mid_nwrite_t2_v2) in
      let st2 = snd(mid_nwrite_t2_v2) in
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

(*** NOTE: after_nabt and after_ncom are not actually needed here, because in after_nread and after_nwrite, ncom has been invoked, and ncom plays nabort's role when necessary although the nabort function is not actually invoked ***)

  (* let after_nabt_t1 =  *)
  (*   try *)
  (*     Forward.find forward ((state1, state2), "nt, abt, t1") *)
  (*   with Not_found ->  *)
  (*     let post_state = nabort_t1 state1 state2 in  *)
  (*     match check_status post_state 1 with *)
  (*     |	Non_exist -> post_state *)
  (*     |	_ -> begin  *)
  (* 	  (\* print_to_files state1 state2 post_state "abtt1"; *\) *)
  (* 	  Forward.add forward ((state1, state2), "nt, abt, t1") post_state; *)
  (* 	  state_no := (!state_no) + 1; *)
  (* 	  post_state  *)
  (*       end  *)
  (* in *)
  (* 	  printf "No. %d: after_nabt_t1\n%s\n" (!state_no) (print_state_pair (fst(after_nabt_t1)) (snd(after_nabt_t1))); *)

  (* let after_nabt_t2 =  *)
  (*   try *)
  (*     Forward.find forward ((state1, state2), "nt, abt, t2") *)
  (*   with Not_found ->  *)
  (*     let post_state = nabort_t2 state1 state2 in  *)
  (*     match check_status post_state 1 with *)
  (*     |	Non_exist -> post_state *)
  (*     |	_ -> begin  *)
  (* 	  (\* print_to_files state1 state2 post_state "abtt2"; *\) *)
  (* 	  Forward.add forward ((state1, state2), "nt, abt, t2") post_state; *)
  (* 	  state_no := (!state_no) + 1; *)
  (* 	  post_state  *)
  (*       end  *)
  (* in *)
  (* 	  printf "No. %d: after_nabt_t2\n%s\n" (!state_no) (print_state_pair (fst(after_nabt_t2)) (snd(after_nabt_t2))); *)

  (* let after_ncom_t1 =  *)
  (*   try *)
  (*     Forward.find forward ((state1, state2), "nt, com, t1") *)
  (*   with Not_found ->  *)
  (*     let post_state = ncommit_t1 state1 state2 in  *)
  (*     match check_status post_state 1 with *)
  (*     |	Non_exist -> post_state *)
  (*     |	_ -> begin  *)
  (* 	  print_to_files state1 state2 post_state "comt1"; *)
  (* 	  Forward.add forward ((state1, state2), "nt, com, t1") post_state; *)
  (* 	  state_no := (!state_no) + 1; *)
  (* 	  post_state  *)
  (*       end  *)
  (* in *)
  (* 	  printf "No. %d: after_ncom_t1\n%s\n" (!state_no) (print_state_pair (fst(after_ncom_t1)) (snd(after_ncom_t1))); *)

  (* let after_ncom_t2 =  *)
  (*   try *)
  (*     Forward.find forward ((state1, state2), "nt, com, t2") *)
  (*   with Not_found ->  *)
  (*     let post_state = ncommit_t2 state1 state2 in  *)
  (*     match check_status post_state 1 with *)
  (*     |	Non_exist -> post_state *)
  (*     |	_ -> begin  *)
  (* 	  print_to_files state1 state2 post_state "comt2"; *)
  (* 	  Forward.add forward ((state1, state2), "nt, com, t2") post_state; *)
  (* 	  state_no := (!state_no) + 1; *)
  (* 	  post_state  *)
  (*       end  *)
  (* in *)
  (* 	  printf "No. %d: after_ncom_t2\n%s\n" (!state_no) (print_state_pair (fst(after_ncom_t2)) (snd(after_ncom_t2))); *)

  let state_list = [after_tread_t1_v1; after_tread_t1_v2; after_tread_t2_v1; after_tread_t2_v2; after_twrite_t1_v1; after_twrite_t1_v2; after_twrite_t2_v1; after_twrite_t2_v2;
		    (* after_abt_t1; after_abt_t2; *) after_com_one_t1; after_com_one_t2; after_com_two_t1; after_com_two_t2; after_nread_t1_v1; after_nread_t1_v2; after_nread_t2_v1; after_nread_t2_v2; after_nwrite_t1_v1;
		    after_nwrite_t1_v2; after_nwrite_t2_v1; after_nwrite_t2_v2; (* after_nabt_t1; after_nabt_t2; after_ncom_t1; after_ncom_t2; *)
		   ] in

  (* printf "The original state list is:\n"; *)
  (* List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) state_list; *)

  let stateSet = StateSet.empty in
  let newStateSet = List.fold_left (fun acc st -> StateSet.add st acc) stateSet state_list in
  let postStateSet = StateSet.remove non_exist newStateSet in
  (* let finalSet = List.fold_left (fun acc st -> StateSet.remove st acc) postStateSet [after_com_one_t1; after_com_one_t2] in *)
  let newList = StateSet.elements postStateSet in

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
  
  (* let clearNonExist t1 t2 = begin  *)
  (*   match (t1 = emptyState), (t2 = emptyState) with *)
  (*   | true, true -> [] *)
  (*   | true, false -> [t2] *)
  (*   | false, true -> [t1] *)
  (*   | false, false -> [t1; t2] *)
  (* end in *)
  
  (* let cleanAfterCom = clearNonExist after_com_one_t1 after_com_one_t2 in *)
  (* let postStateList = List.rev_append cleanAfterCom finalList in *)

  (*** The states which has an in_com value as non-zero should not be regarded as a final state since the commit action has not finished yet when in_com != 0 ***)
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

(*   ref_loop := (!ref_loop) + 1; *)
(*   printf "loop %d: \n" (!ref_loop); *)
(*   printf "The post states of %s are:\n" (print_state_pair state1 state2); *)
(*   List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) postStateList; *)
(*   printf "And among them the final states are:\n"; *)
(*   List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) finalList; *)

  (postStateList, finalList)
end

let work_ref = ref (StateSet.add init_state_pair (StateSet.empty))
let visit_ref = ref (StateSet.empty)
let work_size = StateSet.cardinal (!work_ref);;

let rec reachable work_list visit_list finalSet = begin
  match work_list, visit_list, finalSet with
  | [], v, fs -> fs
  | hd::tl, v, fs -> begin
      let new_v = hd::v in
      let post_w = fst(get_post_state (fst(hd)) (snd(hd))) in                                   (* get the post states list *)
      let finalStates = snd(get_post_state (fst(hd)) (snd(hd))) in                              (* new *)
      let emptySet = StateSet.empty in
      let finalSet = List.fold_left (fun acc st -> StateSet.add st acc) fs finalStates in       (* new *)
      let visitSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet new_v in       (* the set of visited states *)
      let oldWorkSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet tl in        (* the set of the unvisited states *)
      let oldSet = StateSet.union visitSet oldWorkSet in                                        (* the union set of the visited and the unvisited states *)
      let postSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet post_w in       (* the set of the post states of the current chosen state *)
      let newStates = StateSet.diff postSet oldSet in                                           (* the new states in the post states set compared with the all the visited and unvisited states *)
      let newWorkList = StateSet.elements (StateSet.union oldWorkSet newStates) in              (* the union of the new states and the unvisited states *)
      reachable newWorkList new_v finalSet
  end
end
;;

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

(*let w_file = "../../huml-new/new_read_epsilon_TMESI_automaton.ml"*)
let w_file = "new_read_epsilon_TMESI_automaton.ml"
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


(* eager FlexTM automaton with two variables on one cache line*)

open Printf

type status =  Active | Aborted | Committed |Invalid | Non_exist 
(* type trans = TRead | NRead | TWrite | NWrite | Commit | Abort *)
type var = V1 | V2
type thread = T1 | T2
type cl = CL1 (* Same cache lines in different threads have the same name. Here there is only one cache line per thread *)
type flag = int
type cl_info = thread * cl
type rw_cfl = cl_info option (* Read-write conflict. Here the variable is not included, since only thread and cache line will be checked while aborting or commiting a transaction *)
type wr_cfl = cl_info option (*write-read conflict*)
type ww_cfl = cl_info option (*write-write conflict*)
type var_info = cl * var 
type readSet = var_info option * var_info option
type writeSet = var_info option * var_info option
type cls = TMI | TI | M | E | S | I | N_E (* Non-exist state *)
type tag = int

type state = status * flag * readSet * writeSet * rw_cfl * wr_cfl * ww_cfl * cls
type statePair = state * state
type raw_statePair = tag * statePair

let status_to_string = function | Active -> "active" | Aborted -> "aborted" | Committed -> "committed" |Invalid -> "invalid" | Non_exist -> "non_exist"
let cfl_to_string = function | None -> "n" | Some (T1, CL1) -> "(t1, cl1)" | Some (T2, CL1) -> "(t2, cl1)"
let var_info_to_string = function | None -> "n" | Some (CL1, V1) -> "(cl1, v1)" | Some (CL1, V2) -> "(cl1, v2)"
let thread_to_string = function | None -> "n" | Some T1 -> "t1" | Some T2 -> "t2" 
let flag_to_string = string_of_int
let print_wrSet (vi1, vi2) = "(" ^ var_info_to_string vi1 ^ ", " ^ var_info_to_string vi2 ^ ")" 
let print_rw_cfl cfl = " rw(" ^ cfl_to_string cfl ^ ")" 
let print_wr_cfl cfl = " wr(" ^ cfl_to_string cfl ^ ")" 
let print_ww_cfl cfl = " ww(" ^ cfl_to_string cfl ^ ")" 
let cls_to_string = function | TMI -> "tmi" | TI -> "ti" | M -> "m" | E -> "e" | S -> "s" | I -> "i" | N_E -> "n-e"
let print_cls cls = "(" ^ cls_to_string cls ^ ") " 

let print_state ((sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls): state) = begin
  let sta_s = status_to_string sta in
  let flag_s = flag_to_string flg in
  let rs_s = print_wrSet rs in
  let ws_s = print_wrSet ws in
  let rw_cfl_s = print_rw_cfl rw_cfl in
  let wr_cfl_s = print_wr_cfl wr_cfl in
  let ww_cfl_s = print_ww_cfl ww_cfl in
  let cls_s= print_cls cls in
  sta_s^flag_s^rs_s^ws_s^rw_cfl_s^wr_cfl_s^ww_cfl_s^cls_s
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
      |	_  -> (fst(wr_set), Some (CL1, V2))
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

let cfl_empty cfl = begin
  match cfl with
  | None -> true
  | _ -> false
end

(*** ZYY: checking if the input write set is empty ***)
let ws_empty ws = begin
  match ws with
  | (None, None) -> true
  | _ -> false
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
let tread_t1 (vi: var_info) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  (* when flg is not equal to 0, it means that the tx in being non-tx read/written and not finished yet. All the tx operations should serialize after the non-tx ones *)
  if (flg1 != 0) || (flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      let sta = Active in
      let rs = add_vi vi rs1 in
      match cl_in_set vi ws2 with
      |	true -> 
	  begin
	    let (rw_cfl, wr_cfl) = ((add_ci (T2, CL1) rw_cfl1), (add_ci (T1, CL1) wr_cfl2)) in
	    (1, ((sta, flg1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, cls2_f)))
	  end
      |	_ ->
	  begin
	    let (rw_cfl, wr_cfl) = (rw_cfl1, wr_cfl2) in
	    (0, ((sta, flg1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, cls2_f)))
	  end

    (*   let (rw_cfl, wr_cfl) =  *)
    (* 	match cl_in_set vi ws2 with *)
    (* 	| true -> ((add_ci (T2, CL1) rw_cfl1), (add_ci (T1, CL1) wr_cfl2)) *)
    (* 	| _ -> (rw_cfl1, wr_cfl2) *)
    (*   in *)
    (* ((sta, flg1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, cls2_f)) *)
    end
  end
end

let tread_t2 (vi: var_info) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (flg1 != 0) || (flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      let sta = Active in
      let rs = add_vi vi rs2 in
      match cl_in_set vi ws1 with
      |	true -> 
	  begin
	    let (rw_cfl, wr_cfl) = ((add_ci (T1, CL1) rw_cfl2), (add_ci (T2, CL1) wr_cfl1)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, cls1_f), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, cls2_f)))
	  end
      |	_ ->
	  begin
	    let (rw_cfl, wr_cfl) = (rw_cfl2, wr_cfl1) in
	    (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, cls1_f), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, cls2_f)))
	  end

    (* else begin *)
    (*   let sta = Active in *)
    (*   let rs = add_vi vi rs2 in *)
    (*   let (rw_cfl, wr_cfl) = *)
    (* 	match cl_in_set vi ws1 with *)
    (* 	| true -> ((add_ci (T1, CL1) rw_cfl2), (add_ci (T2, CL1) wr_cfl1)) *)
    (* 	| _ -> (rw_cfl2, wr_cfl1) *)
    (*   in *)
    (* ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, cls1_f), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, cls2_f)) *)
    end
  end
end

let twrite_t1 (vi: var_info) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (flg1 != 0) || (flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      let sta = Active in
      let ws = add_vi vi ws1 in
      match (cl_in_set vi rs2), (cl_in_set vi ws2) with
      |	true, true -> 
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T2, CL1) wr_cfl1), (add_ci (T1, CL1) rw_cfl2)) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, CL1) ww_cfl1), (add_ci (T1, CL1) ww_cfl2)) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, cls2_f)))
	  end
      |	true, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T2, CL1) wr_cfl1), (add_ci (T1, CL1) rw_cfl2)) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, cls2_f)))
	  end
      | _, true ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl1, rw_cfl2) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, CL1) ww_cfl1), (add_ci (T1, CL1) ww_cfl2)) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, cls2_f)))
	  end
      | _, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl1, rw_cfl2) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (0, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, cls2_f)))
	  end

    (*   let (wr_cfl, rw_cfl) = *)
    (* 	match cl_in_set vi rs2 with *)
    (* 	| true -> ((add_ci (T2, CL1) wr_cfl1), (add_ci (T1, CL1) rw_cfl2)) *)
    (* 	| _ -> (wr_cfl1, rw_cfl2) *)
    (*   in *)
    (*   let (ww_cfl1_f, ww_cfl2_f) = *)
    (* 	match cl_in_set vi ws2 with *)
    (* 	| true -> ((add_ci (T2, CL1) ww_cfl1), (add_ci (T1, CL1) ww_cfl2)) *)
    (* 	| _ -> (ww_cfl1, ww_cfl2) *)
    (*   in *)
    (* ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, cls2_f)) *)
    end
  end
end

let twrite_t2 (vi: var_info) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (flg1 != 0) || (flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls2_f, cls1_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      let sta = Active in
      let ws = add_vi vi ws2 in
      (* let (wr_cfl, rw_cfl) = *)
      match (cl_in_set vi rs1), (cl_in_set vi ws1) with
      |	true, true -> 
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T1, CL1) wr_cfl2), (add_ci (T2, CL1) rw_cfl1))  in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, CL1) ww_cfl1), (add_ci (T1, CL1) ww_cfl2)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, cls1_f), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, cls2_f)))
	  end
      |	true, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T1, CL1) wr_cfl2), (add_ci (T2, CL1) rw_cfl1))  in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, cls1_f), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, cls2_f)))
	  end
      | _, true ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl2, rw_cfl1) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, CL1) ww_cfl1), (add_ci (T1, CL1) ww_cfl2)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, cls1_f), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, cls2_f)))
	  end
      | _, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl2, rw_cfl1) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2)  in
	    (0, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, cls1_f), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, cls2_f)))
	  end
    end
  end
end

let abort_t1 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta1 != Active && sta1 != Invalid) || flg1 != 0) || flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      let sta = Aborted in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = None in
      let wr_cfl = None in
      let ww_cfl = None in
      (0, ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2_f)))
    end
  end
end

let abort_t2 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta2 != Active && sta2 != Invalid) || flg1 != 0) || flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      let sta = Aborted in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = None in
      let wr_cfl = None in
      let ww_cfl = None in
      (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1_f), (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)))
    end
  end
end

let commit_t1 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta1 = Aborted || flg1 != 0) || flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      (*** ZYY: when a transaction is to commit, all of its conflict tables should be empty ***)
      if ((((cfl_empty rw_cfl1) != true) || ((cfl_empty wr_cfl1) != true)) || ((cfl_empty ww_cfl1) != true)) then
	(0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
      else begin
	let sta = Committed in
	let rs = (None, None) in
	let ws = (None, None) in
	let rw_cfl = None in
	let wr_cfl = None in
	let ww_cfl = None in
	(0, ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2_f)))
	
	(* let if_abort = begin *)
      	(*   match wr_cfl1, rw_cfl2, ww_cfl1, ww_cfl2 with *)
        (*   | Some (T2, _), Some (T1, _), _, _ -> true (\* the other tx should be aborted only when the cfl in both threads are unempty, because sometimes the neighbour can be aborted or committed *\) *)
      	(*   | _, _, Some (T2, _), Some (T1, _) -> true *)
      	(*   | _, _, _, _ -> false *)
	(* end in *)

	(* let empty_rw = begin *)
      	(*   match rw_cfl1 with *)
      	(*   | Some (T2, _) -> true *)
      	(*   | _ -> false *)
	(* end in *)
      
      (* let aborted_part = snd (abort_t2 (sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in *)
      (* note the order of the arguments of aborted_cls. abroted_cls always abort the first thread so here cls2 should be the first *)
      (* let abt_cls2 = fst(aborted_cls cls2 cls1) in *)
      (* let invalid_state = (Invalid, 0, (None, None), (None, None), None, None, None, abt_cls2) in *)
      (* match if_abort, empty_rw with *)
      (* |	true, _ -> ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), invalid_state) *)
      (* |	_, true -> ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, None, ww_cfl2, cls2_f)) *)
      (* |	_, _ -> ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2_f)) *)
      end
    end
  end
end

let commit_t2 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta2 = Aborted || flg1 != 0) || flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls2_f, cls1_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      if ((((cfl_empty rw_cfl2) != true) || ((cfl_empty wr_cfl2) != true)) || ((cfl_empty ww_cfl2) != true)) then
	(0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
      else begin
	let sta = Committed in
	let rs = (None, None) in
	let ws = (None, None) in
	let rw_cfl = None in
	let wr_cfl = None in
	let ww_cfl = None in
	(0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1_f), (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)))
      (* 	let if_abort = begin *)
      (* 	  match wr_cfl2, rw_cfl1, ww_cfl2, ww_cfl1 with *)
      (*     | Some (T1, _), Some (T2, _), _, _ -> true *)
      (* 	  | _, _, Some (T1, _), Some (T2, _) -> true *)
      (* 	  | _, _, _, _ -> false *)
      (* 	end in *)
	
      (* 	let empty_rw = begin *)
      (* 	  match rw_cfl2 with *)
      (* 	  | Some (T1, _) -> true *)
      (* 	  | _ -> false *)
      (* 	end in *)
	
      (* (\* let aborted_part = snd (abort_t1 (sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in *\) *)
      (* 	let abt_cls1 = fst(aborted_cls cls1 cls2) in *)
      (* 	let invalid_state = (Invalid, 0, (None, None), (None, None), None, None, None, abt_cls1) in *)
      (* 	match if_abort, empty_rw with *)
      (* 	|	true, _ -> (invalid_state, (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)) *)
      (* 	|	_, true -> ((sta1, flg1, rs1, ws1, rw_cfl1, None, ww_cfl1, cls1_f), (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)) *)
      (* 	|	_, _ -> ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1_f), (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)) *)
	end
      end
  end
end

let nread_t1 (vi: var_info) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta1 == Active || flg1 != 0) || flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      let sta = Active in
      let flg1_f = 1 in
      let rs = add_vi vi rs1 in
      let (rw_cfl, wr_cfl) =
	match cl_in_set vi ws2 with
	| true -> ((add_ci (T2, CL1) rw_cfl1), (add_ci (T1, CL1) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    (0, ((sta, flg1_f, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, cls2_f)))
    end
  end
end

let nread_t2 (vi: var_info) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta2 == Active || flg1 != 0) || flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      let sta =  Active in
      let flg2_f = 1 in
      let rs = add_vi vi rs2 in
      let (rw_cfl, wr_cfl) =
	match cl_in_set vi ws1 with
	| true -> ((add_ci (T1, CL1) rw_cfl2), (add_ci (T2, CL1) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, cls1_f), (sta, flg2_f, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, cls2_f)))
    end
  end
end

let nwrite_t1 (vi: var_info) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta1 == Active || flg1 != 0) || flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    (0, ((sta, flg1_f, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, cls1_f), (sta2, flg2_f, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, cls2_f)))
    end
  end
end

let nwrite_t2 (vi: var_info) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta2 == Active || flg1 != 0) || flg2 != 0) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    (0, ((sta1, flg1_f, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, cls1_f), (sta, flg2_f, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, cls2_f)))
    end
  end
end

let nabort_t1 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (((sta1 != Invalid || flg1 != 2) || flg2 != 1)) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    (0, ((sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2_f)))
  end
end

let nabort_t2 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if ((sta2 != Invalid || flg2 != 2) || flg1 != 1) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1_f), (sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)))
  end
end

let ncommit_t1 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (sta1 != Active || flg1 != 1) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    let invalid_state = (Invalid, 0, (None, None), (None, None), None, None, None, abt_cls2) in
    if flg2 = 2 then (0, ((sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), invalid_state))
    else (0,((sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls1_f), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2_f)))
  end
end

let ncommit_t2 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2): state) = begin
  if (sta2 != Active || flg2 != 1) then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
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
    let invalid_state = (Invalid, 0, (None, None), (None, None), None, None, None, abt_cls1) in
    if flg1 = 2 then (0, (invalid_state, (sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)))
    else (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1_f), (sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls2_f)))
  end
end

(* The invisible_read functions are actually the same as tx_read/nt_read functions. The only difference is that some information such as cache line state doesn't need to be checked. Only the rs needs *)
(* to be updated. So it takes shorter time to invoke an inv_read function than a normal read function. Meanwhile, an inv_read function can also be regarded as a normal read funcion in the automaton *)

let inv_read_t1 (vi: var_info) (tag, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2))) = begin
  let rs = add_vi vi rs1 in
(*** ZYY: inv_read means that all the variables in this cache line are read. in this program there is only one cache line in each transaction, which means all the variables of the transaction are read. ***)
(*** so only need to check if the other transaction's write set is empty if one wants to know if there is read-write conflict ***)
  match ws_empty ws2 with
  (*** ZYY: tag should be kept here instead of using 0, since there might have been write-write conflict before and the tag was 1 already ***)
  | true -> (tag, ((sta1, flg1, rs, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)))
  | _ -> (1, ((sta1, flg1, rs, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)))
end

let inv_read_t2 (vi: var_info) (tag, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2))) = begin
  let rs = add_vi vi rs2 in
  match ws_empty ws1 with
  | true -> (tag, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, rs, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)))
  | _ -> (1, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1), (sta2, flg2, rs, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)))
end

let get_status state = begin
  match state with
  | (sta, _, _, _, _, _, _, _) -> sta
end

let check_status state_pair i = begin
  match i with
  | 1 -> get_status (fst(state_pair))
  | _ -> get_status (snd(state_pair))
end

let check_raw_status raw_statePair = get_status (fst(snd(raw_statePair)));; 

let get_flg state = begin
  match state with
  | (_, flg, _, _, _, _, _, _) -> flg
end

(*** ZYY: check if the tag is 1 ***)
let abt_one raw_statePair = begin
  match raw_statePair with
  | (1, _) -> true
  | (_, _) -> false
end

let inv_to_abt (sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls) = begin
  let sta_f = Aborted in
  (sta_f, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls)
end

module StateSet = Set.Make(struct type t = (state * state) let compare = Pervasives.compare end)
module RawStateSet = Set.Make(struct type t = raw_statePair let compare = Pervasives.compare end)
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

let forward : raw_statePair Forward.t = Forward.create 0
let states : int States.t = States.create 0

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

let init_state_pair = ((Committed, 0, (None, None), (None, None), None, None, None, I), (Committed, 0, (None, None), (None, None), None, None, None, I))
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

let ref_loop = ref 0
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


(* Each read/write actually includes an invisible read. So the hash table records both the read/write operation and the invisible read operation. The output of the get_post_state function is the list *)
(* of the states after both read/write and invisible read. E.g., When after_tread_t1_v1 state S, A_S is after tread_t1_v1 S and then invisibly tread_t1_v2 S. So A_S will be in the list of the output. *)
(* But both post states of (tread_t1_v1 S) and (tread_t1_v2 S) are counted into the number of the states of the TMESI *)

(* only invoking print_states_to_file in the non-final states, then adding the final states in from the visted list like the reference automaton is not correct here. Because an after_trd_t1_v1 *)
(* final state will not change when a trd_t1_v1 applies on it. This is not a final state but is the same as a final one, so it will be printed out in the TMESI_States.ml. While the same state which *)
(* appears in the visisted list will also be printed out, without invoking print_states_to_file because all the visited list is simply copied into the file. A secure way is to invoke print_states_to_file *)
(* whenever there can be a new state generated in get_post_state. The duplicated states will filtered out by print_states_to_file *)
let get_post_state state1 state2 = begin
  (* The single tx read operation. I.e., without the invisible read operation *)
  let ref_state_list = ref [] in
  let (trd_t1_v1: raw_statePair) =
    let st =
      try
	Forward.find forward ((state1, state2), "tx, rd, t1, v1, cl1")
      with Not_found ->
	let post_state = tread_t1 (CL1, V1) state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
  	  (* old: print_to_files state1 state2 post_state "rdt1v1"; *)
  	    Forward.add forward ((state1, state2), "tx, rd, t1, v1, cl1") post_state;
  	  (* old: print_states_to_file post_state; *)
  	    post_state
        end
    in
    let prt_st = snd(st) in
    print_to_files state1 state2 prt_st "rdt1v1";
    print_states_to_file prt_st;
    st
  in
  	  (* printf "No. %d: trd_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(trd_t1_v1)) (snd(trd_t1_v1))); *)

  (* The real after_tread_t1_v1 is trd_t1_v1 plus invisible trd_t1_v2 *)
  (*** ZYY: trd_t1_v1_st doesn't need to be added into ref_state_list since it is not a final state ***)
  let after_tread_t1_v1 =
    let st1 = fst(snd(trd_t1_v1)) in
    let st2 = snd(snd(trd_t1_v1)) in
    
    let post_state = 
      if (check_raw_status trd_t1_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
      else begin
	try
  	  Forward.find forward ((st1, st2), "inv, rd, t1, v2, cl1")
	with Not_found ->
  	  let post_state = inv_read_t1 (CL1, V2) trd_t1_v1 in
  	  match check_raw_status post_state with
  	  | Non_exist -> post_state
  	  | _ -> begin
  	      (* old: print_to_files st1 st2 post_state "rdt1v2"; *)
  	      Forward.add forward ((st1, st2), "inv, rd, t1, v2, cl1") post_state;
  	      (* old: print_states_to_file post_state; *)
  	      post_state
          end
      end
    in

    let after_tread_t1_v1_st = snd(post_state) in
    if (not(abt_one post_state)) then begin
      ref_state_list := after_tread_t1_v1_st::(!ref_state_list);
      if (check_raw_status post_state != Non_exist) then begin
     	print_to_files st1 st2 after_tread_t1_v1_st "rdt1v2";
     	print_states_to_file after_tread_t1_v1_st
      end else ()
    end
    else begin
       (*** ZYY: after_tread_t1_v1 doesn't need to be added into ref_state_list since it is not a final state ***)
      let abt_t1_tread_t1_v1 = snd(abort_t1 (fst(after_tread_t1_v1_st)) (snd(after_tread_t1_v1_st))) in
      let abt_t2_tread_t1_v1 = snd(abort_t2 (fst(after_tread_t1_v1_st)) (snd(after_tread_t1_v1_st))) in
      ref_state_list := abt_t1_tread_t1_v1::(abt_t2_tread_t1_v1::(!ref_state_list));
      print_to_files state1 state2 after_tread_t1_v1_st "rdt1v2";
      print_states_to_file after_tread_t1_v1_st;
      print_to_files (fst(after_tread_t1_v1_st)) (snd(after_tread_t1_v1_st)) abt_t1_tread_t1_v1 "abtt1";
      print_states_to_file abt_t1_tread_t1_v1;
      print_to_files (fst(after_tread_t1_v1_st)) (snd(after_tread_t1_v1_st)) abt_t2_tread_t1_v1 "abtt2";
      (* (\*** debugging ***\) printf "printed: abtt2, %s %s \n-> %s\n" (print_state (fst(after_tread_t1_v1_st))) (print_state (snd(after_tread_t1_v1_st))) (print_state_pair (fst(abt_t2_tread_t1_v1)) (snd(abt_t2_tread_t1_v1))); *)
      print_states_to_file abt_t2_tread_t1_v1
    end
  in
  	  (* printf "No. %d: after_tread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t1_v1)) (snd(after_tread_t1_v1))); *)

  let trd_t1_v2 =
    let st =
      try
	Forward.find forward ((state1, state2), "tx, rd, t1, v2, cl1")
      with Not_found ->
	let post_state = tread_t1 (CL1, V2) state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
  	  (* old: print_to_files state1 state2 post_state "rdt1v2"; *)
  	    Forward.add forward ((state1, state2), "tx, rd, t1, v2, cl1") post_state;
  	  (* old: print_states_to_file post_state; *)
  	    post_state
        end
    in
    let prt_st = snd(st) in
    print_to_files state1 state2 prt_st "rdt1v2";
    print_states_to_file prt_st;
    st
  in
(*   	  printf "No. %d: trd_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(trd_t1_v2)) (snd(trd_t1_v2))); *)


  let after_tread_t1_v2 =
    let st1 = fst(snd(trd_t1_v2)) in
    let st2 = snd(snd(trd_t1_v2)) in

    let post_state = 
    if (check_raw_status trd_t1_v2) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
  	Forward.find forward ((st1, st2), "inv, rd, t1, v1, cl1")
      with Not_found ->
  	let post_state = inv_read_t1 (CL1, V1) trd_t1_v2 in
  	match check_raw_status post_state with
  	| Non_exist -> post_state
  	| _ -> begin
  	    (* old: print_to_files st1 st2 post_state "rdt1v1"; *)
  	    Forward.add forward ((st1, st2), "inv, rd, t1, v1, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
          end
    end
    in

    let after_tread_t1_v2_st = snd(post_state) in
    if (not(abt_one post_state)) then begin
      ref_state_list := after_tread_t1_v2_st::(!ref_state_list);
      if (check_raw_status post_state != Non_exist) then begin
     	print_to_files st1 st2 after_tread_t1_v2_st "rdt1v1";
     	print_states_to_file after_tread_t1_v2_st
      end else ()
    end
    else begin
      let abt_t1_tread_t1_v2 = snd(abort_t1 (fst(after_tread_t1_v2_st)) (snd(after_tread_t1_v2_st))) in
      let abt_t2_tread_t1_v2 = snd(abort_t2 (fst(after_tread_t1_v2_st)) (snd(after_tread_t1_v2_st))) in
      ref_state_list := abt_t1_tread_t1_v2::(abt_t2_tread_t1_v2::(!ref_state_list));
      print_to_files state1 state2 after_tread_t1_v2_st "rdt1v1";
      print_states_to_file after_tread_t1_v2_st;
      print_to_files (fst(after_tread_t1_v2_st)) (snd(after_tread_t1_v2_st)) abt_t1_tread_t1_v2 "abtt1";
      print_states_to_file abt_t1_tread_t1_v2;
      print_to_files (fst(after_tread_t1_v2_st)) (snd(after_tread_t1_v2_st)) abt_t2_tread_t1_v2 "abtt2";
      (* (\*** debugging ***\) printf "printed: abtt2, %s %s \n-> %s\n" (print_state (fst(after_tread_t1_v2_st))) (print_state (snd(after_tread_t1_v2_st))) (print_state_pair (fst(abt_t2_tread_t1_v2)) (snd(abt_t2_tread_t1_v2))); *)
      print_states_to_file abt_t2_tread_t1_v2
    end
  in
  	  (* printf "No. %d: after_tread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t1_v2)) (snd(after_tread_t1_v2))); *)

  let trd_t2_v1 =
    let st =
      try
	Forward.find forward ((state1, state2), "tx, rd, t2, v1, cl1")
      with Not_found ->
	let post_state = tread_t2 (CL1, V1) state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
  	    (* old: print_to_files state1 state2 post_state "rdt2v1"; *)
  	    Forward.add forward ((state1, state2), "tx, rd, t2, v1, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
        end
    in
    let prt_st = snd(st) in
    print_to_files state1 state2 prt_st "rdt2v1";
    print_states_to_file prt_st;
    st
  in
  	  (* printf "No. %d: trd_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(trd_t2_v1)) (snd(trd_t2_v1))); *)

  let after_tread_t2_v1 =
    let st1 = fst(snd(trd_t2_v1)) in
    let st2 = snd(snd(trd_t2_v1)) in

    let post_state = 
    if (check_raw_status trd_t2_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
  	Forward.find forward ((st1, st2), "inv, rd, t2, v2, cl1")
      with Not_found ->
  	let post_state = inv_read_t2 (CL1, V2) trd_t2_v1 in
  	match check_raw_status post_state with
  	| Non_exist -> post_state
  	| _ -> begin
  	    (* old: print_to_files st1 st2 post_state "rdt2v2"; *)
  	    Forward.add forward ((st1, st2), "inv, rd, t2, v2, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
          end
    end
    in

    let after_tread_t2_v1_st = snd(post_state) in
    if (not(abt_one post_state)) then begin
      ref_state_list := after_tread_t2_v1_st::(!ref_state_list);
      if (check_raw_status post_state != Non_exist) then begin
     	print_to_files st1 st2 after_tread_t2_v1_st "rdt2v2";
     	print_states_to_file after_tread_t2_v1_st
      end else ()
    end
    else begin
      let abt_t1_tread_t2_v1 = snd(abort_t1 (fst(after_tread_t2_v1_st)) (snd(after_tread_t2_v1_st))) in
      let abt_t2_tread_t2_v1 = snd(abort_t2 (fst(after_tread_t2_v1_st)) (snd(after_tread_t2_v1_st))) in
      ref_state_list := abt_t1_tread_t2_v1::(abt_t2_tread_t2_v1::(!ref_state_list));
      print_to_files state1 state2 after_tread_t2_v1_st "rdt2v2";
      print_states_to_file after_tread_t2_v1_st;
      print_to_files (fst(after_tread_t2_v1_st)) (snd(after_tread_t2_v1_st)) abt_t1_tread_t2_v1 "abtt1";
      print_states_to_file abt_t1_tread_t2_v1;
      print_to_files (fst(after_tread_t2_v1_st)) (snd(after_tread_t2_v1_st)) abt_t2_tread_t2_v1 "abtt2";
      (* (\*** debugging ***\) printf "printed: abtt2, %s %s \n-> %s\n" (print_state (fst(after_tread_t2_v1_st))) (print_state (snd(after_tread_t2_v1_st))) (print_state_pair (fst(abt_t2_tread_t2_v1)) (snd(abt_t2_tread_t2_v1))); *)
      print_states_to_file abt_t2_tread_t2_v1
    end
  in
  	  (* printf "No. %d: after_tread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t2_v1)) (snd(after_tread_t2_v1))); *)

  let trd_t2_v2 =
    let st =
      try
	Forward.find forward ((state1, state2), "tx, rd, t2, v2, cl1")
      with Not_found ->
	let post_state = tread_t2 (CL1, V2) state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
  	    (* old: print_to_files state1 state2 post_state "rdt2v2"; *)
  	    Forward.add forward ((state1, state2), "tx, rd, t2, v2, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
        end
    in
    let prt_st = snd(st) in
    print_to_files state1 state2 prt_st "rdt2v2";
    print_states_to_file prt_st;
    st
  in
  	  (* printf "No. %d: trd_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(trd_t2_v2)) (snd(trd_t2_v2))); *)

  let after_tread_t2_v2 =
    let st1 = fst(snd(trd_t2_v2)) in
    let st2 = snd(snd(trd_t2_v2)) in

    let post_state =
      if (check_raw_status trd_t2_v2) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
      else begin
	try
  	  Forward.find forward ((st1, st2), "inv, rd, t2, v1, cl1")
	with Not_found ->
  	  let post_state = inv_read_t2 (CL1, V1) trd_t2_v2 in
  	  match check_raw_status post_state with
  	  | Non_exist -> post_state
  	  | _ -> begin
  	      (* old: print_to_files st1 st2 post_state "rdt2v1"; *)
  	      Forward.add forward ((st1, st2), "inv, rd, t2, v1, cl1") post_state;
  	      (* old: print_states_to_file post_state; *)
  	      post_state
          end
      end
    in   
   
    let after_tread_t2_v2_st = snd(post_state) in
    if (not(abt_one post_state)) then begin
      ref_state_list := after_tread_t2_v2_st::(!ref_state_list);
      if (check_raw_status post_state != Non_exist) then begin
     	print_to_files st1 st2 after_tread_t2_v2_st "rdt2v1";
     	print_states_to_file after_tread_t2_v2_st
      end else ()
    end
    else begin
      let abt_t1_tread_t2_v2 = snd(abort_t1 (fst(after_tread_t2_v2_st)) (snd(after_tread_t2_v2_st))) in
      let abt_t2_tread_t2_v2 = snd(abort_t2 (fst(after_tread_t2_v2_st)) (snd(after_tread_t2_v2_st))) in
      ref_state_list := abt_t1_tread_t2_v2::(abt_t2_tread_t2_v2::(!ref_state_list));
      print_to_files state1 state2 after_tread_t2_v2_st "rdt2v1";
      print_states_to_file after_tread_t2_v2_st;
      print_to_files (fst(after_tread_t2_v2_st)) (snd(after_tread_t2_v2_st)) abt_t1_tread_t2_v2 "abtt1";
      print_states_to_file abt_t1_tread_t2_v2;
      print_to_files (fst(after_tread_t2_v2_st)) (snd(after_tread_t2_v2_st)) abt_t2_tread_t2_v2 "abtt2";
      print_states_to_file abt_t2_tread_t2_v2
    end
  in
  	  (* printf "No. %d: after_tread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t2_v2)) (snd(after_tread_t2_v2))); *)

  let twr_t1_v1 =
    let st =
      try
	Forward.find forward ((state1, state2), "tx, wr, t1, v1, cl1")
      with Not_found ->
	let post_state = twrite_t1 (CL1, V1) state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
  	    (* old: print_to_files state1 state2 post_state "wrt1v1"; *)
  	    Forward.add forward ((state1, state2), "tx, wr, t1, v1, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
        end
    in	    
    let prt_st = snd(st) in
    print_to_files state1 state2 prt_st "wrt1v1";
    print_states_to_file prt_st;
    st
  in
  	  (* printf "No. %d: twr_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(twr_t1_v1)) (snd(twr_t1_v1))); *)
  
  let after_twrite_t1_v1 =
    let st1 = fst(snd(twr_t1_v1)) in
    let st2 = snd(snd(twr_t1_v1)) in

    let post_state =
      if (check_raw_status twr_t1_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
      else begin
	try
  	  Forward.find forward ((st1, st2), "inv, rd, t1, v2, cl1")
	with Not_found ->
  	  let post_state = inv_read_t1 (CL1, V2) twr_t1_v1 in
  	  match check_raw_status post_state with
  	  | Non_exist -> post_state
  	  | _ -> begin
  	      (* old: print_to_files st1 st2 post_state "rdt1v2"; *)
  	      Forward.add forward ((st1, st2), "inv, rd, t1, v2, cl1") post_state;
  	      (* old: print_states_to_file post_state; *)
  	      post_state
          end
      end
    in

    let after_twrite_t1_v1_st = snd(post_state) in
    if (not(abt_one post_state)) then begin
      ref_state_list := after_twrite_t1_v1_st::(!ref_state_list);
      if (check_raw_status post_state != Non_exist) then begin
     	print_to_files st1 st2 after_twrite_t1_v1_st "wrt1v2";
     	print_states_to_file after_twrite_t1_v1_st
      end else ()
    end
    else begin
      let abt_t1_twrite_t1_v1 = snd(abort_t1 (fst(after_twrite_t1_v1_st)) (snd(after_twrite_t1_v1_st))) in
      let abt_t2_twrite_t1_v1 = snd(abort_t2 (fst(after_twrite_t1_v1_st)) (snd(after_twrite_t1_v1_st))) in
      ref_state_list := abt_t1_twrite_t1_v1::(abt_t2_twrite_t1_v1::(!ref_state_list));
      print_to_files state1 state2 after_twrite_t1_v1_st "wrt1v2";
      print_states_to_file after_twrite_t1_v1_st;
      print_to_files (fst(after_twrite_t1_v1_st)) (snd(after_twrite_t1_v1_st)) abt_t1_twrite_t1_v1 "abtt1";
      print_states_to_file abt_t1_twrite_t1_v1;
      print_to_files (fst(after_twrite_t1_v1_st)) (snd(after_twrite_t1_v1_st)) abt_t2_twrite_t1_v1 "abtt2";
      print_states_to_file abt_t2_twrite_t1_v1
    end
  in
  	  (* printf "No. %d: after_twrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t1_v1)) (snd(after_twrite_t1_v1))); *)

  let twr_t1_v2 =
    let st =
      try
	Forward.find forward ((state1, state2), "tx, wr, t1, v2, cl1")
      with Not_found ->
	let post_state = twrite_t1 (CL1, V2) state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
  	    (* old: print_to_files state1 state2 post_state "wrt1v2"; *)
  	    Forward.add forward ((state1, state2), "tx, wr, t1, v2, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
        end
    in
    let prt_st = snd(st) in
    print_to_files state1 state2 prt_st "wrt1v2";
    print_states_to_file prt_st;
    st
  in

  	  (* printf "No. %d: twr_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(twr_t1_v2)) (snd(twr_t1_v2))); *)

  let after_twrite_t1_v2 =
    let st1 = fst(snd(twr_t1_v2)) in
    let st2 = snd(snd(twr_t1_v2)) in

    let post_state =
      if (check_raw_status twr_t1_v2) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
      else begin
	try
  	  Forward.find forward ((st1, st2), "inv, rd, t1, v1, cl1")
      with Not_found ->
  	let post_state = inv_read_t1 (CL1, V1) twr_t1_v2 in
  	match check_raw_status post_state with
  	| Non_exist -> post_state
  	| _ -> begin
  	    (* old: print_to_files st1 st2 post_state "rdt1v1"; *)
  	    Forward.add forward ((st1, st2), "inv, rd, t1, v1, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
        end
      end
    in

    let after_twrite_t1_v2_st = snd(post_state) in
    if (not(abt_one post_state)) then begin
      ref_state_list := after_twrite_t1_v2_st::(!ref_state_list);
      if (check_raw_status post_state != Non_exist) then begin
     	print_to_files st1 st2 after_twrite_t1_v2_st "wrt1v1";
     	print_states_to_file after_twrite_t1_v2_st
      end else ()
    end
    else begin
      let abt_t1_twrite_t1_v2 = snd(abort_t1 (fst(after_twrite_t1_v2_st)) (snd(after_twrite_t1_v2_st))) in
      let abt_t2_twrite_t1_v2 = snd(abort_t2 (fst(after_twrite_t1_v2_st)) (snd(after_twrite_t1_v2_st))) in
      ref_state_list := abt_t1_twrite_t1_v2::(abt_t2_twrite_t1_v2::(!ref_state_list));
      print_to_files state1 state2 after_twrite_t1_v2_st "wrt1v1";
      print_states_to_file after_twrite_t1_v2_st;
      print_to_files (fst(after_twrite_t1_v2_st)) (snd(after_twrite_t1_v2_st)) abt_t1_twrite_t1_v2 "abtt1";
      print_states_to_file abt_t1_twrite_t1_v2;
      print_to_files (fst(after_twrite_t1_v2_st)) (snd(after_twrite_t1_v2_st)) abt_t2_twrite_t1_v2 "abtt2";
      print_states_to_file abt_t2_twrite_t1_v2
    end
  in
  (* 	  printf "No. %d: after_twrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t1_v2)) (snd(after_twrite_t1_v2))); *)

  let twr_t2_v1 =
    let st =
      try
	Forward.find forward ((state1, state2), "tx, wr, t2, v1, cl1")
    with Not_found ->
      let post_state = twrite_t2 (CL1, V1) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
  	  (* old: print_to_files state1 state2 post_state "wrt2v1"; *)
  	  Forward.add forward ((state1, state2), "tx, wr, t2, v1, cl1") post_state;
  	  (* old: print_states_to_file post_state; *)
  	  post_state
      end
    in
    let prt_st = snd(st) in
    print_to_files state1 state2 prt_st "wrt2v1";
    print_states_to_file prt_st;
    st
  in
  	  (* printf "No. %d: twr_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(twr_t2_v1)) (snd(twr_t2_v1))); *)

  let after_twrite_t2_v1 =
    let st1 = fst(snd(twr_t2_v1)) in
    let st2 = snd(snd(twr_t2_v1)) in
    
    let post_state =
      if (check_raw_status twr_t2_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
      else begin
	try
  	  Forward.find forward ((st1, st2), "inv, rd, t2, v2, cl1")
	with Not_found ->
  	  let post_state = inv_read_t2 (CL1, V2) twr_t2_v1 in
  	  match check_raw_status post_state with
  	  | Non_exist -> post_state
  	  | _ -> begin
  	      (* old: print_to_files st1 st2 post_state "rdt2v2"; *)
  	      Forward.add forward ((st1, st2), "inv, rd, t2, v2, cl1") post_state;
  	      (* old: print_states_to_file post_state; *)
  	      post_state
          end
      end
    in

    let after_twrite_t2_v1_st = snd(post_state) in
    if (not(abt_one post_state)) then begin
      ref_state_list := after_twrite_t2_v1_st::(!ref_state_list);
      if (check_raw_status post_state != Non_exist) then begin
     	print_to_files st1 st2 after_twrite_t2_v1_st "wrt2v2";
     	print_states_to_file after_twrite_t2_v1_st
      end else ()
    end
    else begin
      let abt_t1_twrite_t2_v1 = snd(abort_t1 (fst(after_twrite_t2_v1_st)) (snd(after_twrite_t2_v1_st))) in
      let abt_t2_twrite_t2_v1 = snd(abort_t2 (fst(after_twrite_t2_v1_st)) (snd(after_twrite_t2_v1_st))) in
      ref_state_list := abt_t1_twrite_t2_v1::(abt_t2_twrite_t2_v1::(!ref_state_list));
      print_to_files state1 state2 after_twrite_t2_v1_st "wrt2v2";
      print_states_to_file after_twrite_t2_v1_st;
      print_to_files (fst(after_twrite_t2_v1_st)) (snd(after_twrite_t2_v1_st)) abt_t1_twrite_t2_v1 "abtt1";
      print_states_to_file abt_t1_twrite_t2_v1;
      print_to_files (fst(after_twrite_t2_v1_st)) (snd(after_twrite_t2_v1_st)) abt_t2_twrite_t2_v1 "abtt2";
      print_states_to_file abt_t2_twrite_t2_v1
    end
  in
  	  (* printf "No. %d: after_twrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t2_v1)) (snd(after_twrite_t2_v1))); *)

  let twr_t2_v2 =
    let st =
      try
	Forward.find forward ((state1, state2), "tx, wr, t2, v2, cl1")
      with Not_found ->
	let post_state = twrite_t2 (CL1, V2) state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
  	    (* old: print_to_files state1 state2 post_state "wrt2v2"; *)
  	    Forward.add forward ((state1, state2), "tx, wr, t2, v2, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
        end
    in
    let prt_st = snd(st) in
    print_to_files state1 state2 prt_st "wrt2v2";
    print_states_to_file prt_st;
    st
  in
  	  (* printf "No. %d: twr_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(twr_t2_v2)) (snd(twr_t2_v2))); *)

  let after_twrite_t2_v2 =
    let st1 = fst(snd(twr_t2_v2)) in
    let st2 = snd(snd(twr_t2_v2)) in
    let post_state =
      if (check_raw_status twr_t2_v2) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
      else begin
	try
  	  Forward.find forward ((st1, st2), "inv, rd, t2, v1, cl1")
	with Not_found ->
  	  let post_state = inv_read_t2 (CL1, V1) twr_t2_v2 in
  	  match check_raw_status post_state with
  	  | Non_exist -> post_state
  	  | _ -> begin
  	    (* old: print_to_files st1 st2 post_state "rdt2v1"; *)
  	    Forward.add forward ((st1, st2), "inv, rd, t2, v1, cl1") post_state;
  	    (* old: print_states_to_file post_state; *)
  	    post_state
          end
      end
    in
    
    let after_twrite_t2_v2_st = snd(post_state) in
    if (not(abt_one post_state)) then begin
      ref_state_list := after_twrite_t2_v2_st::(!ref_state_list);
      if (check_raw_status post_state != Non_exist) then begin
     	print_to_files st1 st2 after_twrite_t2_v2_st "wrt2v1";
     	print_states_to_file after_twrite_t2_v2_st
      end else ()
    end
    else begin
      let abt_t1_twrite_t2_v2 = snd(abort_t1 (fst(after_twrite_t2_v2_st)) (snd(after_twrite_t2_v2_st))) in
      let abt_t2_twrite_t2_v2 = snd(abort_t2 (fst(after_twrite_t2_v2_st)) (snd(after_twrite_t2_v2_st))) in
      print_to_files state1 state2 after_twrite_t2_v2_st "wrt2v1";
      print_states_to_file after_twrite_t2_v2_st;
      print_to_files (fst(after_twrite_t2_v2_st)) (snd(after_twrite_t2_v2_st)) abt_t1_twrite_t2_v2 "abtt1";
      print_states_to_file abt_t1_twrite_t2_v2;
      print_to_files (fst(after_twrite_t2_v2_st)) (snd(after_twrite_t2_v2_st)) abt_t2_twrite_t2_v2 "abtt2";
      print_states_to_file abt_t2_twrite_t2_v2;
      ref_state_list := abt_t1_twrite_t2_v2::(abt_t2_twrite_t2_v2::(!ref_state_list));
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
  
  let after_com_t1 =
    let post_state =
      try
	Forward.find forward ((state1, state2), "tx, com, t1")
      with Not_found ->
	let post_state = commit_t1 state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    (* old: print_to_files state1 state2 post_state "comt1"; *)
	    Forward.add forward ((state1, state2), "tx, com, t1") post_state;
	    (* old: print_states_to_file post_state; *)
	    post_state
        end
    in
        
    let after_com_t1_st = snd(post_state) in
    ref_state_list := after_com_t1_st::(!ref_state_list);
    if (check_raw_status post_state != Non_exist) then begin
      print_to_files state1 state2 after_com_t1_st "comt1";
      print_states_to_file after_com_t1_st
    end else ()
  in
	  (* printf "No. %d: after_com_t1\n%s\n" (!state_no) (print_state_pair (fst(after_com_t1)) (snd(after_com_t1))); *)

  let after_com_t2 =
    let post_state =
      try
	Forward.find forward ((state1, state2), "tx, com, t2")
      with Not_found ->
	let post_state = commit_t2 state1 state2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    (* print_to_files state1 state2 post_state "comt2"; *)
	    Forward.add forward ((state1, state2), "tx, com, t2") post_state;
	    (* print_states_to_file post_state; *)
	    post_state
        end
    in

    let after_com_t2_st = snd(post_state) in
    ref_state_list := after_com_t2_st::(!ref_state_list);
    if (check_raw_status post_state != Non_exist) then begin
      print_to_files state1 state2 after_com_t2_st "comt2";
      print_states_to_file after_com_t2_st
    end else ()
  in
	  (* printf "No. %d: after_com_t2\n%s\n" (!state_no) (print_state_pair (fst(after_com_t2)) (snd(after_com_t2))); *)

(* first non-tx read v1/v2 in t1 *)
  let nrd_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v1, cl1")
    with Not_found ->
      let post_state = nread_t1 (CL1, V1) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
	  print_to_files state1 state2 st "rdt1v1";
	  Forward.add forward ((state1, state2), "nt, rd, t1, v1, cl1") post_state;
	  print_states_to_file st;
	  post_state
        end
  in
(* 	  printf "No. %d: nrd_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(nrd_t1_v1)) (snd(nrd_t1_v1))); *)

(* then invisibly read the other variable v1/v2 in the same cache line *)
  let mid_nread_t1_v1 =
    let st = snd(nrd_t1_v1) in
    let st1 = fst(st) in
    let st2 = snd(st) in
    if (check_raw_status nrd_t1_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
	Forward.find forward ((st1, st2), "inv, rd, t1, v2, cl1")
      with Not_found ->
	let post_state = inv_read_t1 (CL1, V2) nrd_t1_v1 in
	  match check_raw_status post_state with
	  | Non_exist -> post_state
	  | _ -> begin
	      let mst = snd(post_state) in
	      print_to_files st1 st2 mst "rdt1v2";
	      Forward.add forward ((st1, st2), "inv, rd, t1, v2, cl1") post_state;
	      print_states_to_file mst;
	      post_state
          end
    end
  in
	  (* printf "No. %d: mid_nread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(mid_nread_t1_v1)) (snd(mid_nread_t1_v1))); *)

(* at last commit the non-tx read *)
  let after_nread_t1_v1 =
    if (check_raw_status mid_nread_t1_v1) == Non_exist then () (* ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)) *)
    else begin
      let st1 = fst(snd(mid_nread_t1_v1)) in
      let st2 = snd(snd(mid_nread_t1_v1)) in
      let raw_after_nrd_t1_v1 =
	try
	  Forward.find forward ((st1, st2), "nt, com, t1")
	with Not_found ->
	  let post_state = ncommit_t1 st1 st2 in
	  match check_raw_status post_state with
	  | Non_exist -> post_state
	  | _ -> begin
	      (* print_to_files st1 st2 post_state "comt1"; *)
	      Forward.add forward ((st1, st2), "nt, com, t1") post_state;
	      (* print_states_to_file post_state; *)
	      post_state
          end
      in
      let after_nrd_t1_v1 = snd(raw_after_nrd_t1_v1) in
      ref_state_list := after_nrd_t1_v1::(!ref_state_list);
      print_to_files st1 st2 after_nrd_t1_v1 "comt1";
      print_states_to_file after_nrd_t1_v1
    end
  in
	  (* printf "No. %d: after_nread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t1_v1)) (snd(after_nread_t1_v1))); *)

  let nrd_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v2, cl1")
    with Not_found ->
      let post_state = nread_t1 (CL1, V2) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
	  print_to_files state1 state2 st "rdt1v2";
	  Forward.add forward ((state1, state2), "nt, rd, t1, v2, cl1") post_state;
	  print_states_to_file st;
	  post_state
        end
  in
	  (* printf "No. %d: nrd_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(nrd_t1_v2)) (snd(nrd_t1_v2))); *)

  let mid_nread_t1_v2 =
    let st = snd(nrd_t1_v2) in
    let st1 = fst(st) in
    let st2 = snd(st) in
    if (check_raw_status nrd_t1_v2) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
	Forward.find forward ((st1, st2), "inv, rd, t1, v1, cl1")
      with Not_found ->
	let post_state = inv_read_t1 (CL1, V1) nrd_t1_v2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    let mst = snd(post_state) in
	    print_to_files st1 st2 mst "rdt1v1";
	    Forward.add forward ((st1, st2), "inv, rd, t1, v1, cl1") post_state;
	    print_states_to_file mst;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(mid_nread_t1_v2)) (snd(mid_nread_t1_v2))); *)

  let after_nread_t1_v2 =
    if (check_raw_status mid_nread_t1_v2) == Non_exist then () (* ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)) *)
    else begin
      let st1 = fst(snd(mid_nread_t1_v2)) in
      let st2 = snd(snd(mid_nread_t1_v2)) in
      let raw_after_nrd_t1_v2 =
	try
	  Forward.find forward ((st1, st2), "nt, com, t1")
	with Not_found ->
	  let post_state = ncommit_t1 st1 st2 in
	  match check_raw_status post_state with
	  | Non_exist -> post_state
	  | _ -> begin
	    (* print_to_files st1 st2 post_state "comt1"; *)
	      Forward.add forward ((st1, st2), "nt, com, t1") post_state;
	    (* print_states_to_file post_state; *)
	      post_state
          end
      in
      let after_nrd_t1_v2 = snd(raw_after_nrd_t1_v2) in
      ref_state_list := after_nrd_t1_v2::(!ref_state_list);
      print_to_files st1 st2 after_nrd_t1_v2 "comt1";
      print_states_to_file after_nrd_t1_v2
    end
  in
	  (* printf "No. %d: after_nread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t1_v1)) (snd(after_nread_t1_v1))); *)

  let nrd_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v1, cl1")
    with Not_found ->
      let post_state = nread_t2 (CL1, V1) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
	  print_to_files state1 state2 st "rdt2v1";
	  Forward.add forward ((state1, state2), "nt, rd, t2, v1, cl1") post_state;
	  print_states_to_file st;
	  post_state
        end
  in
	  (* printf "No. %d: nrd_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(nrd_t2_v1)) (snd(nrd_t2_v1))); *)

  let mid_nread_t2_v1 =
    let st = snd(nrd_t2_v1) in
    let st1 = fst(st) in
    let st2 = snd(st) in
    if (check_raw_status nrd_t2_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
	Forward.find forward ((st1, st2), "inv, rd, t2, v2, cl1")
      with Not_found ->
	let post_state = inv_read_t2 (CL1, V2) nrd_t2_v1 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    let mst = snd(post_state) in
	    print_to_files st1 st2 mst "rdt2v2";
	    Forward.add forward ((st1, st2), "inv, rd, t2, v2, cl1") post_state;
	    print_states_to_file mst;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(mid_nread_t2_v1)) (snd(mid_nread_t2_v1))); *)

  let after_nread_t2_v1 =
    if (check_raw_status mid_nread_t2_v1) == Non_exist then () (* ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)) *)
    else begin
      let st1 = fst(snd(mid_nread_t2_v1)) in
      let st2 = snd(snd(mid_nread_t2_v1)) in
      let raw_after_nrd_t2_v1 =
      try
	Forward.find forward ((st1, st2), "nt, com, t2")
      with Not_found ->
	let post_state = ncommit_t2 st1 st2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    (* print_to_files st1 st2 post_state "comt2"; *)
	    Forward.add forward ((st1, st2), "nt, com, t2") post_state;
	    (* print_states_to_file post_state; *)
	    post_state
          end
      in
      let after_nrd_t2_v1 = snd(raw_after_nrd_t2_v1) in
      ref_state_list := after_nrd_t2_v1::(!ref_state_list);
      print_to_files st1 st2 after_nrd_t2_v1 "comt2";
      print_states_to_file after_nrd_t2_v1
    end
  in
	  (* printf "No. %d: after_nread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t2_v1)) (snd(after_nread_t2_v1))); *)

  let nrd_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v2, cl1")
    with Not_found ->
      let post_state = nread_t2 (CL1, V2) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
	  print_to_files state1 state2 st "rdt2v2";
	  Forward.add forward ((state1, state2), "nt, rd, t2, v2, cl1") post_state;
	  print_states_to_file st;
	  post_state
        end
  in
(* 	  printf "No. %d: nrd_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(nrd_t2_v2)) (snd(nrd_t2_v2))); *)

  let mid_nread_t2_v2 =
    let st = snd(nrd_t2_v2) in
    let st1 = fst(st) in
    let st2 = snd(st) in
    if (check_raw_status nrd_t2_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
	Forward.find forward ((st1, st2), "inv, rd, t2, v1, cl1")
      with Not_found ->
	let post_state = inv_read_t2 (CL1, V1) nrd_t2_v2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    let mst = snd(post_state) in
	    print_to_files st1 st2 mst "rdt2v1";
	    Forward.add forward ((st1, st2), "inv, rd, t2, v1, cl1") post_state;
	    print_states_to_file mst;
	    post_state
          end
    end
  in
(* 	  printf "No. %d: mid_nread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(mid_nread_t2_v2)) (snd(mid_nread_t2_v2))); *)

  let after_nread_t2_v2 =
    if (check_raw_status mid_nread_t2_v2) == Non_exist then () (* ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)) *)
    else begin
      let st1 = fst(snd(mid_nread_t2_v2)) in
      let st2 = snd(snd(mid_nread_t2_v2)) in
      let raw_after_nrd_t2_v2 =
	try
	  Forward.find forward ((st1, st2), "nt, com, t2")
	with Not_found ->
	  let post_state = ncommit_t2 st1 st2 in
	  match check_raw_status post_state with
	  | Non_exist -> post_state
	  | _ -> begin
	      (* print_to_files st1 st2 post_state "comt2"; *)
	      Forward.add forward ((st1, st2), "nt, com, t2") post_state;
	      (* print_states_to_file post_state; *)
	      post_state
          end
      in
      let after_nrd_t2_v2 = snd(raw_after_nrd_t2_v2) in
      ref_state_list := after_nrd_t2_v2::(!ref_state_list);
      print_to_files st1 st2 after_nrd_t2_v2 "comt2";
      print_states_to_file after_nrd_t2_v2;
    end
  in
(* 	  printf "No. %d: after_nread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t2_v2)) (snd(after_nread_t2_v2))); *)

  let nwr_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v1, cl1")
    with Not_found ->
      let post_state = nwrite_t1 (CL1, V1) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
	  print_to_files state1 state2 st "wrt1v1";
	  Forward.add forward ((state1, state2), "nt, wr, t1, v1, cl1") post_state;
	  print_states_to_file st;
	  post_state
        end
  in
(* 	  printf "No. %d: nwr_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(nwr_t1_v1)) (snd(nwr_t1_v1))); *)
  
(*   (\* printf "The state of nwr_t1_v1 is:\n%s\n" (print_state_pair (fst(nwr_t1_v1)) (snd(nwr_t1_v1))); *\) *)

  let mid_nwrite_t1_v1 =
    let st = snd(nwr_t1_v1) in
    let st1 = fst(st) in
    let st2 = snd(st) in
    if (check_raw_status nwr_t1_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
	Forward.find forward ((st1, st2), "inv, rd, t1, v2, cl1")
      with Not_found ->
	let post_state = inv_read_t1 (CL1, V2) nwr_t1_v1 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    let mst = snd(post_state) in
	    print_to_files st1 st2 mst "rdt1v2";
	    Forward.add forward ((st1, st2), "inv, rd, t1, v2, cl1") post_state;
	    print_states_to_file mst;
	    post_state
          end
    end
  in
	  (* printf "No. %d: mid_nwrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(mid_nwrite_t1_v1)) (snd(mid_nwrite_t1_v1))); *)

  let after_nwrite_t1_v1 =
    if (check_raw_status mid_nwrite_t1_v1) == Non_exist then () (* ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)) *)
    else begin
      let st1 = fst(snd(mid_nwrite_t1_v1)) in
      let st2 = snd(snd(mid_nwrite_t1_v1)) in
      let raw_after_nwr_t1_v1 =
	try
	  Forward.find forward ((st1, st2), "nt, com, t1")
	with Not_found ->
	  let post_state = ncommit_t1 st1 st2 in
	  match check_raw_status post_state with
	  | Non_exist -> post_state
	  | _ -> begin
	      (* print_to_files st1 st2 post_state "comt1"; *)
	      Forward.add forward ((st1, st2), "nt, com, t1") post_state;
	      (* print_states_to_file post_state; *)
	      post_state
          end
      in
      let after_nwr_t1_v1 = snd(raw_after_nwr_t1_v1) in
      ref_state_list := after_nwr_t1_v1::(!ref_state_list);
      print_to_files st1 st2 after_nwr_t1_v1 "comt1";
      print_states_to_file after_nwr_t1_v1;
    end
  in
(* 	  printf "No. %d: after_nwrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t1_v1)) (snd(after_nwrite_t1_v1))); *)

  let nwr_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v2, cl1")
    with Not_found ->
      let post_state = nwrite_t1 (CL1, V2) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
	  print_to_files state1 state2 st "wrt1v2";
	  Forward.add forward ((state1, state2), "nt, wr, t1, v2, cl1") post_state;
	  print_states_to_file st;
	  post_state
        end
  in
(* 	  printf "No. %d: nwr_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(nwr_t1_v2)) (snd(nwr_t1_v2))); *)

(*   (\* printf "The state of after_nwrite_t1_v1 is:\n%s\n" (print_state_pair (fst(after_nwrite_t1_v1)) (snd(after_nwrite_t1_v1))); *\) *)

  let mid_nwrite_t1_v2 =
    let st = snd(nwr_t1_v2) in
    let st1 = fst(st) in
    let st2 = snd(st) in
    if (check_raw_status nwr_t1_v2) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
	Forward.find forward ((st1, st2), "inv, rd, t1, v1, cl1")
      with Not_found ->
	let post_state = inv_read_t1 (CL1, V1) nwr_t1_v2 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    let mst = snd(post_state) in
	    print_to_files st1 st2 mst "rdt1v1";
	    Forward.add forward ((st1, st2), "inv, rd, t1, v1, cl1") post_state;
	    print_states_to_file mst;
	    post_state
          end
     end
  in
(* 	  printf "No. %d: mid_nwrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(mid_nwrite_t1_v2)) (snd(mid_nwrite_t1_v2))); *)

  let after_nwrite_t1_v2 =
    if (check_raw_status mid_nwrite_t1_v2) == Non_exist then () (* ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)) *)
    else begin
      let st1 = fst(snd(mid_nwrite_t1_v2)) in
      let st2 = snd(snd(mid_nwrite_t1_v2)) in
      let raw_after_nwr_t1_v2 =
	try
	  Forward.find forward ((st1, st2), "nt, com, t1")
	with Not_found ->
	  let post_state = ncommit_t1 st1 st2 in
	  match check_raw_status post_state with
	  | Non_exist -> post_state
	  | _ -> begin
	      (* print_to_files st1 st2 post_state "comt1"; *)
	      Forward.add forward ((st1, st2), "nt, com, t1") post_state;
	      (* print_states_to_file post_state; *)
	      post_state
          end
      in
      let after_nwr_t1_v2 = snd(raw_after_nwr_t1_v2) in
      ref_state_list := after_nwr_t1_v2::(!ref_state_list);
      print_to_files st1 st2 after_nwr_t1_v2 "comt1";
      print_states_to_file after_nwr_t1_v2;
    end
  in
(* 	  printf "No. %d: after_nwrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t1_v2)) (snd(after_nwrite_t1_v2))); *)

  let nwr_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v1, cl1")
    with Not_found ->
      let post_state = nwrite_t2 (CL1, V1) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
	  print_to_files state1 state2 st "wrt2v1";
	  Forward.add forward ((state1, state2), "nt, wr, t2, v1, cl1") post_state;
	  print_states_to_file st;
	  post_state
        end
  in
	  (* printf "No. %d: nwr_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(nwr_t2_v1)) (snd(nwr_t2_v1))); *)

  let mid_nwrite_t2_v1 =
    let st = snd(nwr_t2_v1) in
    let st1 = fst(st) in
    let st2 = snd(st) in
    if (check_raw_status nwr_t2_v1) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
	Forward.find forward ((st1, st2), "inv, rd, t2, v2, cl1")
      with Not_found ->
	let post_state = inv_read_t2 (CL1, V2) nwr_t2_v1 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    let mst = snd(post_state) in
	    print_to_files st1 st2 mst "rdt2v2";
	    Forward.add forward ((st1, st2), "inv, rd, t2, v2, cl1") post_state;
	    print_states_to_file mst;
	    post_state
          end
    end
  in
(* 	  printf "No. %d: mid_nwrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(mid_nwrite_t2_v1)) (snd(mid_nwrite_t2_v1))); *)

  let after_nwrite_t2_v1 =
    if (check_raw_status mid_nwrite_t2_v1) == Non_exist then () (* ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)) *)
    else begin
      let st1 = fst(snd(mid_nwrite_t2_v1)) in
      let st2 = snd(snd(mid_nwrite_t2_v1)) in
      let raw_after_nwr_t2_v1 =
	try
	  Forward.find forward ((st1, st2), "nt, com, t2")
	with Not_found ->
	  let post_state = ncommit_t2 st1 st2 in
	  match check_raw_status post_state with
	  | Non_exist -> post_state
	  | _ -> begin
	      (* print_to_files st1 st2 post_state "comt2"; *)
	      Forward.add forward ((st1, st2), "nt, com, t2") post_state;
	      (* print_states_to_file post_state; *)
	      post_state
          end
      in
      let after_nwr_t2_v1 = snd(raw_after_nwr_t2_v1) in
      ref_state_list := after_nwr_t2_v1::(!ref_state_list);
      print_to_files st1 st2 after_nwr_t2_v1 "comt2";
      print_states_to_file after_nwr_t2_v1;
    end
  in
(* 	  printf "No. %d: after_nwrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t2_v1)) (snd(after_nwrite_t2_v1))); *)

  let nwr_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v2, cl1")
    with Not_found ->
      let post_state = nwrite_t2 (CL1, V2) state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
	  print_to_files state1 state2 st "wrt2v2";
	  Forward.add forward ((state1, state2), "nt, wr, t2, v2, cl1") post_state;
	  print_states_to_file st;
	  post_state
        end
  in
(* 	  printf "No. %d: nwr_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(nwr_t2_v2)) (snd(nwr_t2_v2))); *)

  let mid_nwrite_t2_v2 =
    let st = snd(nwr_t2_v1) in
    let st1 = fst(st) in
    let st2 = snd(st) in
    if (check_raw_status nwr_t2_v2) == Non_exist then (0, ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)))
    else begin
      try
	Forward.find forward ((st1, st2), "inv, rd, t2, v1, cl1")
      with Not_found ->
	let post_state = inv_read_t2 (CL1, V1) nwr_t2_v1 in
	match check_raw_status post_state with
	| Non_exist -> post_state
	| _ -> begin
	    let mst = snd(post_state) in
	    print_to_files st1 st2 mst "rdt2v1";
	    Forward.add forward ((st1, st2), "inv, rd, t2, v1, cl1") post_state;
	    print_states_to_file mst;
	    post_state
          end
    end
  in
(* 	  printf "No. %d: mid_nwrite_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(mid_nwrite_t2_v2)) (snd(mid_nwrite_t2_v2))); *)

  let after_nwrite_t2_v2 =
    if (check_raw_status mid_nwrite_t2_v2) == Non_exist then () (* ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I)) *)
    else begin
      let st1 = fst(snd(mid_nwrite_t2_v2)) in
      let st2 = snd(snd(mid_nwrite_t2_v2)) in
      let raw_after_nwr_t2_v2 =
	try
	  Forward.find forward ((st1, st2), "nt, com, t2")
	with Not_found ->
	  let post_state = ncommit_t2 st1 st2 in
	  match check_raw_status post_state with
	  | Non_exist -> post_state
	  | _ -> begin
	      (* print_to_files st1 st2 post_state "comt2"; *)
	      Forward.add forward ((st1, st2), "nt, com, t2") post_state;
	      (* print_states_to_file post_state; *)
	      post_state
          end
      in
      let after_nwr_t2_v2 = snd(raw_after_nwr_t2_v2) in
      ref_state_list := after_nwr_t2_v2::(!ref_state_list);
      print_to_files st1 st2 after_nwr_t2_v2 "comt2";
      print_states_to_file after_nwr_t2_v2;
    end
  in
(* 	  printf "No. %d: after_nwrite_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t2_v2)) (snd(after_nwrite_t2_v2))); *)

(*** NOTE: atter_nabt and after_ncom are not actually needed here, because in after_nread and after_nwrite, ncom has been invoked, and ncom plays nabort's role when necessary although the nabort function is not actually invoked ***)

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

(*   let state_list = [after_tread_t1_v1; after_tread_t1_v2; after_tread_t2_v1; after_tread_t2_v2; after_twrite_t1_v1; after_twrite_t1_v2; after_twrite_t2_v1; after_twrite_t2_v2; *)
(* 		    (\* after_abt_t1; after_abt_t2; *\) after_com_t1; after_com_t2; after_nread_t1_v1; after_nread_t1_v2; after_nread_t2_v1; after_nread_t2_v2; after_nwrite_t1_v1; *)
(* 		    after_nwrite_t1_v2; after_nwrite_t2_v1; after_nwrite_t2_v2; (\* after_nabt_t1; after_nabt_t2; after_ncom_t1; after_ncom_t2; *\) *)
(* 		   ] in *)

(*   (\* printf "The original state list is:\n"; *\) *)
(*   (\* List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) state_list; *\) *)

after_tread_t1_v1; after_tread_t1_v2; after_tread_t2_v1; after_tread_t2_v2; after_twrite_t1_v1; after_twrite_t1_v2; after_twrite_t2_v1; after_twrite_t2_v2; after_com_t1; after_com_t2;
after_nread_t1_v1; after_nread_t1_v2; after_nread_t2_v1; after_nread_t2_v2; after_nwrite_t1_v1; after_nwrite_t1_v2; after_nwrite_t2_v1; after_nwrite_t2_v2;

  let stateSet = StateSet.empty in
  let newStateSet = List.fold_left (fun acc st -> StateSet.add st acc) stateSet (!ref_state_list) in
  let finalSet = StateSet.remove
      ((Non_exist, 0, (None, None), (None, None), None, None, None, I), (Non_exist, 0, (None, None), (None, None), None, None, None, I))
      newStateSet in
  let newList = StateSet.elements finalSet in
(*   (\*** TODO: add finalList which aborts all the invalid states like that in the reference automaton ***\) *)
(*   (\*** TODO: the cls of the aborted thread should be kept from the invalid state, or the cls should be changed here using the cls switch of aborted_cls ***\) *)
  let finalList = List.fold_left (fun acc (st:statePair) ->
    begin
      let proc_st =
	match (check_status st 1), (check_status st 2) with
	| Invalid, _ -> begin
	    match get_flg (fst(st)) with
	    | 0 -> begin
		let raw_inv =
		  try
		    Forward.find forward (st, "tx, abt, t1")
		  with Not_found ->
		    let aborted = inv_to_abt (fst(st)) in
		    let aborted_st = (aborted, snd(st)) in
		    let tagged_st = (0, aborted_st) in
		    (* print_to_files (fst(st)) (snd(st)) aborted_st "abtt1"; *)
		    (* print_states_to_file st; *)
		    (* print_states_to_file aborted_st; *)
		    Forward.add forward (st, "tx, abt, t1") tagged_st;
		    tagged_st
		in
		snd(raw_inv)
	      end
	    | _ -> begin
		let raw_inv =
		  try
		    Forward.find forward (st, "nt, abt, t1")
		  with Not_found ->
		    let naborted = inv_to_abt (fst(st)) in
		    let naborted_st = (naborted, snd(st)) in
		    let tagged_st = (0, naborted_st) in
		    (* print_to_files (fst(st)) (snd(st)) naborted_st "abtt1"; *)
		    (* print_states_to_file st; *)
		    (* print_states_to_file naborted_st; *)
		    Forward.add forward (st, "nt, abt, t1") tagged_st;
		    tagged_st
		in
		snd(raw_inv)
	      end
	  end
	| _, Invalid -> begin
	    match get_flg (snd(st)) with
	    | 0 -> begin
		let raw_inv =
		  try
		    Forward.find forward (st, "tx, abt, t2")
		  with Not_found ->
		    let aborted = inv_to_abt (snd(st)) in
		    let aborted_st = (fst(st), aborted) in
		    let tagged_st = (0, aborted_st) in
		    (* print_to_files (fst(st)) (snd(st)) aborted_st "abtt2"; *)
		    (* print_states_to_file st; *)
		    (* print_states_to_file aborted_st; *)
		    Forward.add forward (st, "tx, abt, t2") tagged_st;
		    tagged_st
		in 
		snd(raw_inv)
	      end
	    | _ -> begin
		let raw_inv =
		  try
		    Forward.find forward (st, "nt, abt, t2")
		  with Not_found ->
		    let naborted = inv_to_abt (snd(st)) in
		    let naborted_st = (fst(st), naborted) in
		    let tagged_st = (0, naborted_st) in
		    (* print_to_files (fst(st)) (snd(st)) naborted_st "abtt2"; *)
		    (* print_states_to_file st; *)
		    (* print_states_to_file naborted_st; *)
		    Forward.add forward (st, "nt, abt, t2") tagged_st;
		    tagged_st
		in
		snd(raw_inv)
	      end
	  end
	| _, _ -> st
	in proc_st::acc end) [] newList
      in
(*   ref_loop := (!ref_loop) + 1; *)
(*   printf "loop %d: \n" (!ref_loop); *)
(*   printf "The post states of %s are:\n" (print_state_pair state1 state2); *)
(*   List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) finalList; *)
  finalList
end

(* let work_ref = ref (StateSet.add init_state_pair (StateSet.empty)) *)
(* let visit_ref = ref (StateSet.empty) *)
(* let work_size = StateSet.cardinal (!work_ref);; *)
 
(*** ZYY: given a list of states, work_list, and get all the post states of the states in the list ***)
let rec reachable work_list visit_list = begin
  match work_list, visit_list with
  | [], v -> v
  | hd::tl, v -> begin
      let new_v = hd::v in
      let post_w = get_post_state (fst(hd)) (snd(hd)) in
      let emptySet = StateSet.empty in
      let visitSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet new_v in
      let oldWorkSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet tl in
      let oldSet = StateSet.union visitSet oldWorkSet in
      let postSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet post_w in
      let newStates = StateSet.diff postSet oldSet in
      let newWorkList = StateSet.elements (StateSet.union oldWorkSet newStates) in
      reachable newWorkList new_v
  end
end
;;

let visited = reachable [init_state_pair] [];;
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


(* (\********** THE BEGINNING OF THE TESTING CODING **********\) *)

(* (\*** TODO: test all the transition fuctions ***\) *)
(* (\*** TODO: test all the cache line state switching ***\) *)

(* (\*** TODO: test the post states of the initial state, add the printing functionality first and test the rest of the functionalities ***\) *)
(* let state1 = (Active, 0, (None, Some (CL1, V2)), (Some (CL1, V1), None), None, None, None, TMI) *)
(* let state2 = (Committed, 0, (None, None), (None, None), None, None, None, I) *)
(* let post_state = nwrite_t1 (CL1, V2) state1 state2 *)
(* let com_state = ncommit_t1 (fst(post_state)) (snd(post_state)) *)
(* (\* let final_state = nabort_t2 (fst(com_state)) (snd(com_state)) *\) *)

(* let post_str = print_state_pair (fst(post_state)) (snd(post_state));; *)
(* let com_str = print_state_pair (fst(com_state)) (snd(com_state));; *)
(* (\* let final_str = print_state_pair (fst(final_state)) (snd(final_state));; *\) *)
(* (\* printf "The post state pair is:\n%s" post_str;; *\) *)
(* (\* printf "The commit state pair is:\n%s" com_str;; *\) *)
(* (\* printf "The final state pair is:\n%s" final_str;; *\) *)

(* (\* let final = get_post_state (fst(init_state_pair)) (snd(init_state_pair));; *\) *)
(* (\* let final = get_post_state state1 state2;; *\) *)
(* (\* printf "\nThe post states of the initial state are:\n";; *\) *)
(* (\* List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) final;; *\) *)

(* (\* The post states of active0(n, some (cl1, v2))(some (cl1, v1), n) rw(n) wr(n) ww(n)(tmi) active1(some (cl1, v1), some (cl1, v2))(n, n) rw(n) wr(n) ww(n)(i)  are: *\) *)
(* (\* active0(n, some (cl1, v2))(some (cl1, v1), n) rw(n) wr(n) ww(n)(tmi) committed0(n, n)(n, n) rw(n) wr(n) ww(n)(i)  *\) *)
(* (\* active0(n, some (cl1, v2))(some (cl1, v1), n) rw(n) wr(n) ww(n)(tmi) committed0(n, n)(n, n) rw(n) wr(n) ww(n)(i) *\) *)

(* (\********** THE END OF THE TESTING CODING **********\) *)

print_state_file visited o_f;;
(* print_state_file visited o_s;; *)
close_out o_s;;
close_out o_t;;

(*let w_file = "../../huml-new/new_read_eager_TMESI_automaton.ml"*)
let w_file = "new_read_eager_TMESI_automaton.ml"
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


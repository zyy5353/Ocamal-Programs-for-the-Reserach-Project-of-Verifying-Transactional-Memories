(* the eager mode of FlexTM automaton with only one variable per cache line *)

open Printf

type status =  Active | Aborted | Committed |Invalid | Non_exist
type var = V1 | V2
type thread = T1 | T2
type flag = int
type var_info = thread * var
type rw_cfl = (var_info option) * (var_info option) (* Read-write conflict. Here the cache line is not included, since there is only one variable on per cache line in this automaton *)
type wr_cfl = (var_info option) * (var_info option) (*write-read conflict*)
type ww_cfl = (var_info option) * (var_info option) (*write-write conflict*)
type readSet = var option * var option
type writeSet = var option * var option
type cls = TMI | TI | M | E | S | I | N_E (* Non-exist state *)
type cls_set = cls * cls
type tag = int

type state = status * flag * readSet * writeSet * rw_cfl * wr_cfl * ww_cfl * cls_set
type statePair = state * state
type raw_statePair = tag * statePair

let status_to_string = function | Active -> "active" | Aborted -> "aborted" | Committed -> "committed" |Invalid -> "invalid" | Non_exist -> "non_exist"
let var_to_string = function | None -> "n" | Some V1 -> "v1" | Some V2 -> "v2"
let var_info_to_string = function | None -> "n" | Some (T1, V1) -> "(t1, v1)" | Some (T1, V2) -> "(t1, v2)" | Some (T2, V1) -> "(t2, v1)" | Some (T2, V2) -> "(t2, v2)"
let flag_to_string = string_of_int
let print_wrSet (v1, v2) = "(" ^ var_to_string v1 ^ ", " ^ var_to_string v2 ^ ")"
let cfl_to_string (vi1, vi2) = "(" ^ var_info_to_string vi1 ^ ", " ^ var_info_to_string vi2 ^ ")"
let print_rw_cfl cfl = " rw" ^ cfl_to_string cfl (* ^ ")" *)
let print_wr_cfl cfl = " wr" ^ cfl_to_string cfl (* ^ ")"  *)
let print_ww_cfl cfl = " ww" ^ cfl_to_string cfl (* ^ ")"  *)
let cls_to_string = function | TMI -> "tmi" | TI -> "ti" | M -> "m" | E -> "e" | S -> "s" | I -> "i" | N_E -> "n-e"
let print_cls_set cls_set = "(" ^ cls_to_string (fst(cls_set)) ^ ", " ^ cls_to_string (snd(cls_set)) ^ ") "

let print_state ((sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, cls): state) = begin
  let sta_s = status_to_string sta in
  let flag_s = flag_to_string flg in
  let rs_s = print_wrSet rs in
  let ws_s = print_wrSet ws in
  let rw_cfl_s = print_rw_cfl rw_cfl in
  let wr_cfl_s = print_wr_cfl wr_cfl in
  let ww_cfl_s = print_ww_cfl ww_cfl in
  let cls_s= print_cls_set cls in
  sta_s^flag_s^rs_s^ws_s^rw_cfl_s^wr_cfl_s^ww_cfl_s^cls_s
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

let cfl_empty cfl = begin
  match cfl with
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

let tread_t1_v1 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (flg1 != 0) || (flg2 != 0) then
    (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let rs = add_var v rs1 in
      (*** if there is r-w conflict with the other thread, then the first element of the output tuple is 1, else it is 0 ***)
      match var_in_set v ws2 with
      |	true -> 
	  begin
	    let (rw_cfl, wr_cfl) = ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2)) in
	    (1, ((sta, flg1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls1_f, cls12)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls2_f, cls22)))) 
	  end
      |	_ ->
	  begin
	    let (rw_cfl, wr_cfl) = (rw_cfl1, wr_cfl2) in
	    (0, ((sta, flg1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls1_f, cls12)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls2_f, cls22)))) 
	  end
      (* let (rw_cfl, wr_cfl) = *)
      (* 	match var_in_set v ws2 with *)
      (* 	| true -> ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2)) *)
      (* 	| _ -> (rw_cfl1, wr_cfl2) *)
      (* in *)
      (* output *)
    end
  end
end

let tread_t1_v2 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (flg1 != 0) || (flg2 != 0) then
    (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let rs = add_var v rs1 in
      match var_in_set v ws2 with
      |	true -> 
	  begin
	    let (rw_cfl, wr_cfl) = ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2)) in
	    (1, ((sta, flg1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls21, cls2_f)))) 
	  end
      |	_ ->
	  begin
	    let (rw_cfl, wr_cfl) = (rw_cfl1, wr_cfl2) in
	    (0, ((sta, flg1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls21, cls2_f)))) 
	  end
    (*   let (rw_cfl, wr_cfl) = *)
    (* 	match var_in_set v ws2 with *)
    (* 	| true -> ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2)) *)
    (* 	| _ -> (rw_cfl1, wr_cfl2) *)
    (*   in *)
    (* ((sta, flg1, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls21, cls2_f))) *)
    end
  end
end

let tread_t2_v1 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (flg1 != 0) || (flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let rs = add_var v rs2 in
      match var_in_set v ws1 with
      |	true -> 
	  begin
	    let (rw_cfl, wr_cfl) = ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls1_f, cls12)), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls2_f, cls22)))) 
	  end
      |	_ ->
	  begin
	    let (rw_cfl, wr_cfl) = (rw_cfl1, wr_cfl2) in
	    (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls1_f, cls12)), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls2_f, cls22)))) 
	  end
    (*   let (rw_cfl, wr_cfl) = *)
    (* 	match var_in_set v ws1 with *)
    (* 	| true -> ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1)) *)
    (* 	| _ -> (rw_cfl2, wr_cfl1) *)
    (*   in *)
    (* ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls1_f, cls12)), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls2_f, cls22))) *)
    end
  end
end

let tread_t2_v2 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (flg1 != 0) || (flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let rs = add_var v rs2 in
      match var_in_set v ws1 with
      |	true -> 
	  begin
	    let (rw_cfl, wr_cfl) = ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls11, cls1_f)), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls21, cls2_f)))) 
	  end
      |	_ ->
	  begin
	    let (rw_cfl, wr_cfl) = (rw_cfl1, wr_cfl2) in
	    (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls11, cls1_f)), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls21, cls2_f)))) 
	  end
    (*   let (rw_cfl, wr_cfl) = *)
    (* 	match var_in_set v ws1 with *)
    (* 	| true -> ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1)) *)
    (* 	| _ -> (rw_cfl2, wr_cfl1) *)
    (*   in *)
    (* ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls11, cls1_f)), (sta, flg2, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls21, cls2_f))) *)
    end
  end
end

let twrite_t1_v1 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (flg1 != 0) || (flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let ws = add_var v ws1 in
      match (var_in_set v rs2), (var_in_set v ws2) with
      |	true, true -> 
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2)) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls1_f, cls12)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls2_f, cls22))))
	  end
      |	true, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2)) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls1_f, cls12)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls2_f, cls22))))
	  end
      | _, true ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl1, rw_cfl2) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls1_f, cls12)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls2_f, cls22))))
	  end
      | _, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl1, rw_cfl2) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (0, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls1_f, cls12)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls2_f, cls22))))
	  end

    (*   let (wr_cfl, rw_cfl) = *)
    (* 	match var_in_set v rs2 with *)
    (* 	| true -> ((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2)) *)
    (* 	| _ -> (wr_cfl1, rw_cfl2) *)
    (*   in *)
    (*   let (ww_cfl1_f, ww_cfl2_f) = *)
    (* 	match var_in_set v ws2 with *)
    (* 	| true -> ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) *)
    (* 	| _ -> (ww_cfl1, ww_cfl2) *)
    (*   in *)
    (* ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls1_f, cls12)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls2_f, cls22))) *)
    end
  end
end

let twrite_t1_v2 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (flg1 != 0) || (flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let ws = add_var v ws1 in
      match (var_in_set v rs2), (var_in_set v ws2) with
      |	true, true -> 
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2)) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls21, cls2_f))))
	  end
      |	true, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2)) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls21, cls2_f))))
	  end
      | _, true ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl1, rw_cfl2) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) in
	    (1, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls21, cls2_f))))
	  end
      | _, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl1, rw_cfl2) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (0, ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls21, cls2_f))))
	  end

    (*   let (wr_cfl, rw_cfl) = *)
    (* 	match var_in_set v rs2 with *)
    (* 	| true -> ((add_ci (T2, v) wr_cfl1), (add_ci (T1, v) rw_cfl2)) *)
    (* 	| _ -> (wr_cfl1, rw_cfl2) *)
    (*   in *)
    (*   let (ww_cfl1_f, ww_cfl2_f) = *)
    (* 	match var_in_set v ws2 with *)
    (* 	| true -> ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) *)
    (* 	| _ -> (ww_cfl1, ww_cfl2) *)
    (*   in *)
    (* ((sta, flg1, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls21, cls2_f))) *)
    end
  end
end

let twrite_t2_v1 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (flg1 != 0) || (flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let ws = add_var v ws2 in
      match (var_in_set v rs1), (var_in_set v ws1) with
      |	true, true -> 
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1))  in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls1_f, cls12)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls2_f, cls22))))
	  end
      |	true, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1))  in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls1_f, cls12)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls2_f, cls22))))
	  end
      | _, true ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl2, rw_cfl1) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls1_f, cls12)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls2_f, cls22))))
	  end
      | _, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl2, rw_cfl1) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2)  in
	    (0, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls1_f, cls12)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls2_f, cls22))))
	  end

    (*   let (wr_cfl, rw_cfl) = *)
    (* 	match var_in_set v rs1 with *)
    (* 	| true -> ((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1)) *)
    (* 	| _ -> (wr_cfl2, rw_cfl1) *)
    (*   in *)
    (*   let (ww_cfl1_f, ww_cfl2_f) = *)
    (* 	match var_in_set v ws1 with *)
    (* 	| true -> ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) *)
    (* 	| _ -> (ww_cfl1, ww_cfl2) *)
    (*   in *)
    (* ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls1_f, cls12)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls2_f, cls22))) *)
    end
  end
end

let twrite_t2_v2 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (flg1 != 0) || (flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let ws = add_var v ws2 in
      match (var_in_set v rs1), (var_in_set v ws1) with
      |	true, true -> 
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1))  in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls11, cls1_f)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls21, cls2_f))))
	  end
      |	true, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = ((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1))  in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls11, cls1_f)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls21, cls2_f))))
	  end
      | _, true ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl2, rw_cfl1) in
	    let (ww_cfl1_f, ww_cfl2_f) = ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) in
	    (1, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls11, cls1_f)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls21, cls2_f))))
	  end
      | _, _ ->
	  begin
	    let (wr_cfl, rw_cfl) = (wr_cfl2, rw_cfl1) in
	    let (ww_cfl1_f, ww_cfl2_f) = (ww_cfl1, ww_cfl2)  in
	    (0, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls11, cls1_f)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls21, cls2_f))))
	  end


    (*   let (wr_cfl, rw_cfl) = *)
    (* 	match var_in_set v rs1 with *)
    (* 	| true -> ((add_ci (T1, v) wr_cfl2), (add_ci (T2, v) rw_cfl1)) *)
    (* 	| _ -> (wr_cfl2, rw_cfl1) *)
    (*   in *)
    (*   let (ww_cfl1_f, ww_cfl2_f) = *)
    (* 	match var_in_set v ws1 with *)
    (* 	| true -> ((add_ci (T2, v) ww_cfl1), (add_ci (T1, v) ww_cfl2)) *)
    (* 	| _ -> (ww_cfl1, ww_cfl2) *)
    (*   in *)
    (* ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls11, cls1_f)), (sta, flg2, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls21, cls2_f))) *)
    end
  end
end

(*** ZYY: also need to empty the cfl of the unaborted-transaction's ***)

let abort_t1 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta1 = Committed || sta1 = Aborted) || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if ((cls11_f, cls21_f) = (N_E, N_E)||(cls12_f, cls22_f) = (N_E, N_E)) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Aborted in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = (None, None) in
      let wr_cfl = (None, None) in
      let ww_cfl = (None, None) in
      (0, ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, rs2, ws2, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))))
    end
  end
end

let abort_t2 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta2 = Committed || sta2 = Aborted) || flg1 != 0) || flg2 != 0) then begin
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if ((cls11_f, cls21_f) = (N_E, N_E)||(cls12_f, cls22_f) = (N_E, N_E)) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Aborted in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = (None, None) in
      let wr_cfl = (None, None) in
      let ww_cfl = (None, None) in
      (0, ((sta1, flg1, rs1, ws1, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))))
    end
  end
end

let commit_t1 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta1 = Aborted || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
  else begin
    let (cls11_f, cls21_f) =
      match cls11, cls21 with
      (*** The other cache line state cannot be TMI or TI since otherwise it would have been aborted already ***)	
      (* | TMI, TMI -> (M, I) *)
      (* | TMI, TI -> (M, I) *)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, TMI/TI/M/E/S *)
      (* | TI, TMI -> (I, cls21) *)
      |	TI, S -> (I, cls21)
      |	TI, I -> (I, cls21)
      |	TI, _ -> (N_E, N_E) (* TI, TMI/TI/M/E *)
      |	I, _ -> (cls11, cls21) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls11, cls21) (* M/E/S, I *)
      |	S, S -> (cls11, cls21)
      |	S, TI -> (cls11, cls21)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    let (cls12_f, cls22_f) =
      match cls12, cls22 with
      (* | TMI, TMI -> (M, I) *)
      (* | TMI, TI -> (M, I) *)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, TMI/TI/M/E/S *)
      (* | TI, TMI -> (I, cls22) *)
      |	TI, S -> (I, cls22)
      |	TI, I -> (I, cls22)
      |	TI, _ -> (N_E, N_E) (* TI, TMI/TI/M/E *)
      |	I, _ -> (cls12, cls22) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls12, cls22) (* M/E/S, I *)
      |	S, S -> (cls12, cls22)
      |	S, TI -> (cls12, cls22)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if ((cls11_f, cls21_f) = (N_E, N_E)||(cls12_f, cls22_f) = (N_E, N_E)) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      (*** ZYY: when a transaction is to commit, all of its conflict tables should be empty ***)
      if ((((cfl_empty rw_cfl1) != true) || ((cfl_empty wr_cfl1) != true)) || ((cfl_empty ww_cfl1) != true)) then
	(0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
      else begin 	  
      let sta = Committed in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = (None, None) in
      let wr_cfl = (None, None) in
      let ww_cfl = (None, None) in
      (0, ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21_f, cls22_f))))
	end
      
      (* let if_abort = begin *)
      (* 	match wr_cfl1, rw_cfl2, ww_cfl1, ww_cfl2 with *)
      (*   | (Some (T2, _), _), (Some (T1, _), _), _, _ -> true (\* the other tx should be aborted only when the cfl in both threads are unempty, because sometimes the neighbour can be aborted or committed *\) *)
      (*   | (_, Some (T2, _)), (_, Some (T1, _)), _, _ -> true *)
      (* 	| _, _, (Some (T2, _), _), (Some (T1, _), _) -> true *)
      (* 	| _, _, (_, Some (T2, _)), (_, Some (T1, _)) -> true *)
      (* 	| _, _, _, _ -> false *)
      (* end in *)

      (* let empty_wr = begin *)
      (* 	match rw_cfl1 with *)
      (* 	| (Some (T2, _), _) -> true *)
      (* 	| (_, Some (T2, _)) -> true *)
      (* 	| _ -> false *)
      (* end in *)
      
      (* let aborted_part = snd (abort_t2 (sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in *)
      (* note the order of the arguments of aborted_cls. abroted_cls always abort the first thread so here cls2 should be the first *)
      (* let abt_cls21 = fst(aborted_cls cls21 cls11) in *)
      (* let abt_cls22 = fst(aborted_cls cls22 cls12) in *)
      (* let invalid_state = (Invalid, 0,(None, None), (None, None), (None, None), (None, None), (None, None), (abt_cls21, abt_cls22)) in *)
      (* match if_abort, empty_wr with *)
      (* |	true, _ -> ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), invalid_state) *)
      (* |	_, true -> ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, rs2, ws2, rw_cfl2, (None, None), ww_cfl2, (cls21_f, cls22_f))) *)
      (* |	_, _ -> ((sta, flg1, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21_f, cls22_f))) *)
    end
  end
end

let commit_t2 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta2 = Aborted || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
  else begin
    let (cls21_f, cls11_f) =
      match cls21, cls11 with
      (* | TMI, TMI -> (M, I) *)
      (* | TMI, TI -> (M, I) *)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, TMI/TI/M/E/S *)
      (* | TI, TMI -> (I, cls21) *)
      |	TI, S -> (I, cls21)
      |	TI, I -> (I, cls21)
      |	TI, _ -> (N_E, N_E) (* TI, TMI/TI/M/E *)
      |	I, _ -> (cls11, cls21) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls11, cls21) (* M/E/S, I *)
      |	S, S -> (cls11, cls21)
      |	S, TI -> (cls11, cls21)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    let (cls22_f, cls12_f) =
      match cls22, cls12 with
      (* | TMI, TMI -> (M, I) *)
      (* | TMI, TI -> (M, I) *)
      | TMI, I -> (M, I)
      |	TMI, _ -> (N_E, N_E) (* TMI, TMI/TI/M/E/S *)
      (* | TI, TMI -> (I, cls21) *)
      |	TI, S -> (I, cls21)
      |	TI, I -> (I, cls21)
      |	TI, _ -> (N_E, N_E) (* TI, TMI/TI/M/E *)
      |	I, _ -> (cls11, cls21) (* I, TMI/TI/M/E/S/I, for those transactions that have more than one cache line, when the tx commits, the I cache line state doesn't change *)
      |	_, I -> (cls11, cls21) (* M/E/S, I *)
      |	S, S -> (cls11, cls21)
      |	S, TI -> (cls11, cls21)
      |	_, _ -> (N_E, N_E) (* M/E, TMI/TI/M/E/S and S, TMI/M/E *)
    in
    if ((cls11_f, cls21_f) = (N_E, N_E)||(cls12_f, cls22_f) = (N_E, N_E)) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      if ((((cfl_empty rw_cfl2) != true) || ((cfl_empty wr_cfl2) != true)) || ((cfl_empty ww_cfl2) != true)) then
	(0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
      else begin
      let sta = Committed in
      let rs = (None, None) in
      let ws = (None, None) in
      let rw_cfl = (None, None) in
      let wr_cfl = (None, None) in
      let ww_cfl = (None, None) in
      (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11_f, cls12_f)), (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))))
	end
      (* let if_abort = begin *)
      (* 	match wr_cfl2, rw_cfl1, ww_cfl2, ww_cfl1 with *)
      (*   | (Some (T1, _), _), (Some (T2, _), _), _, _ -> true *)
      (*   | (_, Some (T1, _)), (_, Some (T2, _)), _, _ -> true *)
      (* 	| _, _, (Some (T1, _), _), (Some (T2, _), _) -> true *)
      (* 	| _, _, (_, Some (T1, _)), (_, Some (T2, _)) -> true *)
      (* 	| _, _, _, _ -> false *)
      (* end in *)

      (* let empty_wr = begin *)
      (* 	match rw_cfl2 with *)
      (* 	| (Some (T1, _), _) -> true *)
      (* 	| (_, Some (T1, _)) -> true *)
      (* 	| _ -> false *)
      (* end in *)
      
      (* let aborted_part = snd (abort_t1 (sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, cls1) (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, cls2)) in *)
      (* let abt_cls11 = fst(aborted_cls cls11 cls21) in *)
      (* let abt_cls12 = fst(aborted_cls cls12 cls22) in *)
      (* let invalid_state = (Invalid, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (abt_cls11, abt_cls12)) in *)
      (* match if_abort, empty_wr with *)
      (* |	true, _ -> (invalid_state, (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))) *)
      (* |	_, true -> ((sta1, flg1, rs1, ws1, rw_cfl1, (None, None), ww_cfl1, (cls11_f, cls12_f)), (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))) *)
      (* |	_, _ -> ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11_f, cls12_f)), (sta, flg2, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))) *)
    end
  end
end

let nread_t1_v1 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta1 = Active || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let flg1_f = 1 in
      let rs = add_var v rs1 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws2 with
	| true -> ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    (0, ((sta, flg1_f, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls1_f, cls12)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls2_f, cls22))))
    end
  end
end

let nread_t1_v2 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta1 = Active || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta = Active in
      let flg1_f = 1 in
      let rs = add_var v rs1 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws2 with
	| true -> ((add_ci (T2, v) rw_cfl1), (add_ci (T1, v) wr_cfl2))
	| _ -> (rw_cfl1, wr_cfl2)
      in
    (0, ((sta, flg1_f, rs, ws1, rw_cfl, wr_cfl1, ww_cfl1, (cls11, cls1_f)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl, ww_cfl2, (cls21, cls2_f))))
    end
  end
end

let nread_t2_v1 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta2 = Active || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta =  Active in
      let flg2_f = 1 in
      let rs = add_var v rs2 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws1 with
	| true -> ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls1_f, cls12)), (sta, flg2_f, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls2_f, cls22))))
    end
  end
end

let nread_t2_v2 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta2 = Active || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
    else begin
      let sta =  Active in
      let flg2_f = 1 in
      let rs = add_var v rs2 in
      let (rw_cfl, wr_cfl) =
	match var_in_set v ws1 with
	| true -> ((add_ci (T1, v) rw_cfl2), (add_ci (T2, v) wr_cfl1))
	| _ -> (rw_cfl2, wr_cfl1)
      in
    (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl, ww_cfl1, (cls11, cls1_f)), (sta, flg2_f, rs, ws2, rw_cfl, wr_cfl2, ww_cfl2, (cls21, cls2_f))))
    end
  end
end

let nwrite_t1_v1 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta1 = Active || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    (0, ((sta, flg1_f, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls1_f, cls12)), (sta2, flg2_f, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls2_f, cls22))))
    end
  end
end

let nwrite_t1_v2 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta1 = Active || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    (0, ((sta, flg1_f, rs1, ws, rw_cfl1, wr_cfl, ww_cfl1_f, (cls11, cls1_f)), (sta2, flg2_f, rs2, ws2, rw_cfl, wr_cfl2, ww_cfl2_f, (cls21, cls2_f))))
    end
  end
end

let nwrite_t2_v1 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta2 = Active || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    (0, ((sta1, flg1_f, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls1_f, cls12)), (sta, flg2_f, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls2_f, cls22))))
    end
  end
end

let nwrite_t2_v2 (v: var) ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta2 = Active || flg1 != 0) || flg2 != 0) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    if (cls1_f, cls2_f) = (N_E, N_E) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    (0, ((sta1, flg1_f, rs1, ws1, rw_cfl, wr_cfl1, ww_cfl1_f, (cls11, cls1_f)), (sta, flg2_f, rs2, ws, rw_cfl2, wr_cfl, ww_cfl2_f, (cls21, cls2_f))))
    end
  end
end

let nabort_t1 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (((sta1 != Invalid || flg1 != 2) || flg2 != 1)) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    (0, ((sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21_f, cls22_f))))
  end
end

let nabort_t2 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if ((sta2 != Invalid || flg2 != 2) || flg1 != 1) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11_f, cls12_f)), (sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))))
  end
end

let ncommit_t1 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (sta1 != Active || flg1 != 1) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    let invalid_state = (Invalid, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (abt_cls21, abt_cls22)) in
    if flg2 = 2 then (0, ((sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), invalid_state))
    else (0, ((sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls11_f, cls12_f)), (sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21_f, cls22_f))))
  end
end

let ncommit_t2 ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11, cls12)): state) ((sta2, flg2, rs2, ws2, rw_cfl2, wr_cfl2, ww_cfl2, (cls21, cls22)): state) = begin
  if (sta2 != Active || flg2 != 1) then
      (0, ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))))
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
    let invalid_state = (Invalid, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (abt_cls11, abt_cls12)) in
    if flg1 = 2 then (0, (invalid_state, (sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))))
    else (0, ((sta1, flg1, rs1, ws1, rw_cfl1, wr_cfl1, ww_cfl1, (cls11_f, cls12_f)), (sta, flg, rs, ws, rw_cfl, wr_cfl, ww_cfl, (cls21_f, cls22_f))))
  end
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

let init_state_pair = ((Committed, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Committed, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)))
let str_init = print_state_pair (fst(init_state_pair)) (snd(init_state_pair))
let p_init = polish_state "" str_init;;
let t_file = "eager_TMESI_two_cache_line_Transitions.ml"
let f_file = "eager_TMESI_two_cache_line_Final_states.ml"
let s_file = "eager_two_cache_line_States.ml"
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

print_states_to_file init_state_pair;;

let get_post_state state1 state2 = begin
  let ref_state_list = ref [] in

  (*** ZYY: the output list after apply tread_t1_v1 to the input state pair ***)
  let after_tread_t1_v1_lst =
    let raw_tread_t1_v1 =
      try
	Forward.find forward ((state1, state2), "tx, rd, t1, v1")
      with Not_found ->
	let raw_post_state = tread_t1_v1 V1 state1 state2 in
	match check_raw_status raw_post_state with
	| Non_exist -> raw_post_state
	| _ -> begin
	    Forward.add forward ((state1, state2), "tx, rd, t1, v1") raw_post_state;
	    raw_post_state
	    end
     in
     let after_tread_t1_v1 = snd(raw_tread_t1_v1) in
     if (not(abt_one raw_tread_t1_v1)) then begin
       ref_state_list := after_tread_t1_v1::(!ref_state_list);
       if (check_raw_status raw_tread_t1_v1 != Non_exist) then begin
     	 print_to_files state1 state2 after_tread_t1_v1 "rdt1v1";
     	 print_states_to_file after_tread_t1_v1
       end else ()
       (* [after_tread_t1_v1] *)
     end
     else begin
       (*** ZYY: after_tread_t1_v1 doesn't need to be added into ref_state_list since it is not a final state ***)
       print_to_files state1 state2 after_tread_t1_v1 "rdt1v1";
       print_states_to_file after_tread_t1_v1;
       let abt_t1_tread_t1_v1 = snd(abort_t1 (fst(after_tread_t1_v1)) (snd(after_tread_t1_v1))) in
       let abt_t2_tread_t1_v1 = snd(abort_t2 (fst(after_tread_t1_v1)) (snd(after_tread_t1_v1))) in
       ref_state_list := abt_t1_tread_t1_v1::(abt_t2_tread_t1_v1::(!ref_state_list));
       print_to_files (fst(after_tread_t1_v1)) (snd(after_tread_t1_v1)) abt_t1_tread_t1_v1 "abtt1";
       print_states_to_file abt_t1_tread_t1_v1;
       print_to_files (fst(after_tread_t1_v1)) (snd(after_tread_t1_v1)) abt_t2_tread_t1_v1 "abtt2";
       print_states_to_file abt_t2_tread_t1_v1
       (* [abt_t1_tread_t1_v1; abt_t2_tread_t1_v1] *)
     end
  in

  (*     match check_status post_state 1 with *)
  (*     |	Non_exist -> post_state *)
  (*     |	_ -> begin *)
  (*     	  print_to_files state1 state2 post_state "rdt1v1"; *)
  (*     	  Forward.add forward ((state1, state2), "tx, rd, t1, v1") post_state; *)
  (*     	  print_states_to_file post_state; *)
  (*     	  post_state *)
  (*       end *)
  (* in *)
	  (* printf "No. %d: after_tread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t1_v1)) (snd(after_tread_t1_v1))); *)

  let after_tread_t1_v2_lst =
    let raw_tread_t1_v2 =
      try
  	Forward.find forward ((state1, state2), "tx, rd, t1, v2")
      with Not_found ->
  	let raw_post_state = tread_t1_v1 V2 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, rd, t1, v2") raw_post_state;
  	    raw_post_state
        end
    in
    let after_tread_t1_v2 = snd(raw_tread_t1_v2) in
    if (not(abt_one raw_tread_t1_v2)) then begin
       if (check_raw_status raw_tread_t1_v2 != Non_exist) then begin
  	 ref_state_list := after_tread_t1_v2::(!ref_state_list);
  	 print_to_files state1 state2 after_tread_t1_v2 "rdt1v2";
  	 print_states_to_file after_tread_t1_v2
       end else ()
    end
    else begin
      print_to_files state1 state2 after_tread_t1_v2 "rdt1v2";
      print_states_to_file after_tread_t1_v2;
      let abt_t1_tread_t1_v2 = snd(abort_t1 (fst(after_tread_t1_v2)) (snd(after_tread_t1_v2))) in
      let abt_t2_tread_t1_v2 = snd(abort_t2 (fst(after_tread_t1_v2)) (snd(after_tread_t1_v2))) in
      ref_state_list := abt_t1_tread_t1_v2:: (abt_t2_tread_t1_v2::(!ref_state_list));
      print_to_files (fst(after_tread_t1_v2)) (snd(after_tread_t1_v2)) abt_t1_tread_t1_v2 "abtt1";
      print_states_to_file abt_t1_tread_t1_v2;
      print_to_files (fst(after_tread_t1_v2)) (snd(after_tread_t1_v2)) abt_t2_tread_t1_v2 "abtt2";
      print_states_to_file abt_t2_tread_t1_v2
   end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "rdt1v2"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, rd, t1, v2") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)

  	  (* printf "No. %d: after_tread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t1_v2)) (snd(after_tread_t1_v2))); *)

  let after_tread_t2_v1_lst =
    let raw_tread_t2_v1 =
      try
  	Forward.find forward ((state1, state2), "tx, rd, t2, v1")
      with Not_found ->
  	let raw_post_state = tread_t2_v1 V1 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, rd, t2, v1") raw_post_state;
  	    raw_post_state
        end
    in
    let after_tread_t2_v1 = snd(raw_tread_t2_v1) in
    if (not(abt_one raw_tread_t2_v1)) then begin
       if (check_raw_status raw_tread_t2_v1 != Non_exist) then begin
  	 ref_state_list := after_tread_t2_v1::(!ref_state_list);
  	 print_to_files state1 state2 after_tread_t2_v1 "rdt2v1";
  	 print_states_to_file after_tread_t2_v1
       end else ()
    end
    else begin
      print_to_files state1 state2 after_tread_t2_v1 "rdt2v1";
      print_states_to_file after_tread_t2_v1;
      let abt_t1_tread_t2_v1 = snd(abort_t1 (fst(after_tread_t2_v1)) (snd(after_tread_t2_v1))) in
      let abt_t2_tread_t2_v1 = snd(abort_t2 (fst(after_tread_t2_v1)) (snd(after_tread_t2_v1))) in
      ref_state_list := abt_t1_tread_t2_v1::(abt_t2_tread_t2_v1::(!ref_state_list));
      print_to_files (fst(after_tread_t2_v1)) (snd(after_tread_t2_v1)) abt_t1_tread_t2_v1 "abtt1";
      print_states_to_file abt_t1_tread_t2_v1;
      print_to_files (fst(after_tread_t2_v1)) (snd(after_tread_t2_v1)) abt_t2_tread_t2_v1 "abtt2";
      print_states_to_file abt_t2_tread_t2_v1
    end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "rdt2v1"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, rd, t2, v1") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)
  	  (* printf "No. %d: after_tread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t2_v1)) (snd(after_tread_t2_v1))); *)

  let after_tread_t2_v2_lst =
    let raw_tread_t2_v2 =
      try
  	Forward.find forward ((state1, state2), "tx, rd, t2, v2")
      with Not_found ->
  	let raw_post_state = tread_t2_v2 V2 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, rd, t2, v2") raw_post_state;
  	    raw_post_state
        end
    in
    let after_tread_t2_v2 = snd(raw_tread_t2_v2) in
    if (not(abt_one raw_tread_t2_v2)) then begin
       if (check_raw_status raw_tread_t2_v2 != Non_exist) then begin
  	 ref_state_list := after_tread_t2_v2::(!ref_state_list);
  	 print_to_files state1 state2 after_tread_t2_v2 "rdt2v2";
  	 print_states_to_file after_tread_t2_v2
       end else ()
    end
    else begin
      print_to_files state1 state2 after_tread_t2_v2 "rdt2v2";
      print_states_to_file after_tread_t2_v2;
      let abt_t1_tread_t2_v2 = snd(abort_t1 (fst(after_tread_t2_v2)) (snd(after_tread_t2_v2))) in
      let abt_t2_tread_t2_v2 = snd(abort_t2 (fst(after_tread_t2_v2)) (snd(after_tread_t2_v2))) in
      ref_state_list := abt_t1_tread_t2_v2::(abt_t2_tread_t2_v2::(!ref_state_list));
      print_to_files (fst(after_tread_t2_v2)) (snd(after_tread_t2_v2)) abt_t1_tread_t2_v2 "abtt1";
      print_states_to_file abt_t1_tread_t2_v2;
      print_to_files (fst(after_tread_t2_v2)) (snd(after_tread_t2_v2)) abt_t2_tread_t2_v2 "abtt2";
      print_states_to_file abt_t2_tread_t2_v2
    end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "rdt2v2"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, rd, t2, v2") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)

  	  (* printf "No. %d: after_tread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_tread_t2_v2)) (snd(after_tread_t2_v2))); *)

  let after_twrite_t1_v1_lst =
    let raw_twrite_t1_v1 =
      try
  	Forward.find forward ((state1, state2), "tx, wr, t1, v1")
      with Not_found ->
  	let raw_post_state = twrite_t1_v1 V1 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, wr, t1, v1") raw_post_state;
  	    raw_post_state
        end
    in
    let after_twrite_t1_v1 = snd(raw_twrite_t1_v1) in
    if (not(abt_one raw_twrite_t1_v1)) then begin
       if (check_raw_status raw_twrite_t1_v1 != Non_exist) then begin
  	 ref_state_list := after_twrite_t1_v1::(!ref_state_list);
  	 print_to_files state1 state2 after_twrite_t1_v1 "wrt1v1";
  	 print_states_to_file after_twrite_t1_v1
       end else ()
    end
    else begin
      print_to_files state1 state2 after_twrite_t1_v1 "wrt1v1";
      print_states_to_file after_twrite_t1_v1;
      let abt_t1_twrite_t1_v1 = snd(abort_t1 (fst(after_twrite_t1_v1)) (snd(after_twrite_t1_v1))) in
      let abt_t2_twrite_t1_v1 = snd(abort_t2 (fst(after_twrite_t1_v1)) (snd(after_twrite_t1_v1))) in
      ref_state_list := abt_t1_twrite_t1_v1::(abt_t2_twrite_t1_v1::(!ref_state_list));
      print_to_files (fst(after_twrite_t1_v1)) (snd(after_twrite_t1_v1)) abt_t1_twrite_t1_v1 "abtt1";
      print_states_to_file abt_t1_twrite_t1_v1;
      print_to_files (fst(after_twrite_t1_v1)) (snd(after_twrite_t1_v1)) abt_t2_twrite_t1_v1 "abtt2";
      print_states_to_file abt_t2_twrite_t1_v1
    end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "wrt1v1"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, wr, t1, v1") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)

  	  (* printf "No. %d: after_twrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t1_v1)) (snd(after_twrite_t1_v1))); *)

  let after_twrite_t1_v2_lst =
    let raw_twrite_t1_v2 =
      try
  	Forward.find forward ((state1, state2), "tx, wr, t1, v2")
      with Not_found ->
  	let raw_post_state = twrite_t1_v2 V2 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, wr, t1, v2") raw_post_state;
  	    raw_post_state
        end
    in
    let after_twrite_t1_v2 = snd(raw_twrite_t1_v2) in
    if (not(abt_one raw_twrite_t1_v2)) then begin
       if (check_raw_status raw_twrite_t1_v2 != Non_exist) then begin
  	 ref_state_list := after_twrite_t1_v2::(!ref_state_list);
  	 print_to_files state1 state2 after_twrite_t1_v2 "wrt1v2";
  	 print_states_to_file after_twrite_t1_v2
       end else ()
    end
    else begin
      print_to_files state1 state2 after_twrite_t1_v2 "wrt1v2";
      print_states_to_file after_twrite_t1_v2;
      let abt_t1_twrite_t1_v2 = snd(abort_t1 (fst(after_twrite_t1_v2)) (snd(after_twrite_t1_v2))) in
      let abt_t2_twrite_t1_v2 = snd(abort_t2 (fst(after_twrite_t1_v2)) (snd(after_twrite_t1_v2))) in
      ref_state_list := abt_t1_twrite_t1_v2::(abt_t2_twrite_t1_v2::(!ref_state_list));
      print_to_files (fst(after_twrite_t1_v2)) (snd(after_twrite_t1_v2)) abt_t1_twrite_t1_v2 "abtt1";
      print_states_to_file abt_t1_twrite_t1_v2;
      print_to_files (fst(after_twrite_t1_v2)) (snd(after_twrite_t1_v2)) abt_t2_twrite_t1_v2 "abtt2";
      print_states_to_file abt_t2_twrite_t1_v2
    end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "wrt1v2"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, wr, t1, v2") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)

  	  (* printf "No. %d: after_twrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t1_v2)) (snd(after_twrite_t1_v2))); *)

  let after_twrite_t2_v1_lst =
    let raw_twrite_t2_v1 =
      try
  	Forward.find forward ((state1, state2), "tx, wr, t2, v1")
      with Not_found ->
  	let raw_post_state = twrite_t2_v1 V1 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, wr, t2, v1") raw_post_state;
  	    raw_post_state
        end
    in
    let after_twrite_t2_v1 = snd(raw_twrite_t2_v1) in
    if (not(abt_one raw_twrite_t2_v1)) then begin
      ref_state_list := after_twrite_t2_v1::(!ref_state_list);
      if (check_raw_status raw_twrite_t2_v1 != Non_exist) then begin
  	print_to_files state1 state2 after_twrite_t2_v1 "wrt2v1";
  	print_states_to_file after_twrite_t2_v1
      end else ()
    end
    else begin
      print_to_files state1 state2 after_twrite_t2_v1 "wrt2v1";
      print_states_to_file after_twrite_t2_v1;
      let abt_t1_twrite_t2_v1 = snd(abort_t1 (fst(after_twrite_t2_v1)) (snd(after_twrite_t2_v1))) in
      let abt_t2_twrite_t2_v1 = snd(abort_t2 (fst(after_twrite_t2_v1)) (snd(after_twrite_t2_v1))) in
      ref_state_list := abt_t1_twrite_t2_v1::(abt_t2_twrite_t2_v1::(!ref_state_list));
      print_to_files (fst(after_twrite_t2_v1)) (snd(after_twrite_t2_v1)) abt_t1_twrite_t2_v1 "abtt1";
      print_states_to_file abt_t1_twrite_t2_v1;
      print_to_files (fst(after_twrite_t2_v1)) (snd(after_twrite_t2_v1)) abt_t2_twrite_t2_v1 "abtt2";
      print_states_to_file abt_t2_twrite_t2_v1
    end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "wrt2v1"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, wr, t2, v1") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)

  	  (* printf "No. %d: after_twrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_twrite_t2_v1)) (snd(after_twrite_t2_v1))); *)

  let after_twrite_t2_v2_lst =
    let raw_twrite_t2_v2 =
      try
  	Forward.find forward ((state1, state2), "tx, wr, t2, v2")
      with Not_found ->
  	let raw_post_state = twrite_t2_v2 V2 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, wr, t2, v2") raw_post_state;
  	    raw_post_state
        end
    in
    let after_twrite_t2_v2 = snd(raw_twrite_t2_v2) in
    if (not(abt_one raw_twrite_t2_v2)) then begin
       if (check_raw_status raw_twrite_t2_v2 != Non_exist) then begin
  	 ref_state_list := after_twrite_t2_v2::(!ref_state_list);
  	 print_to_files state1 state2 after_twrite_t2_v2 "wrt2v2";
  	 print_states_to_file after_twrite_t2_v2
       end else ()
    end
    else begin
      let abt_t1_twrite_t2_v2 = snd(abort_t1 (fst(after_twrite_t2_v2)) (snd(after_twrite_t2_v2))) in
      let abt_t2_twrite_t2_v2 = snd(abort_t2 (fst(after_twrite_t2_v2)) (snd(after_twrite_t2_v2))) in
      ref_state_list := abt_t1_twrite_t2_v2::(abt_t2_twrite_t2_v2::(!ref_state_list));
      print_to_files state1 state2 after_twrite_t2_v2 "wrt2v2";
      print_states_to_file after_twrite_t2_v2;
      print_to_files (fst(after_twrite_t2_v2)) (snd(after_twrite_t2_v2)) abt_t1_twrite_t2_v2 "abtt1";
      print_states_to_file abt_t1_twrite_t2_v2;
      print_to_files (fst(after_twrite_t2_v2)) (snd(after_twrite_t2_v2)) abt_t2_twrite_t2_v2 "abtt2";
      print_states_to_file abt_t2_twrite_t2_v2
    end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "wrt2v2"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, wr, t2, v2") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)
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
  

  let after_com_t1_lst =
    let raw_com_t1 =
      try
  	Forward.find forward ((state1, state2), "tx, com, t1")
      with Not_found ->
  	let raw_post_state = commit_t1 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, com, t1") raw_post_state;
  	    raw_post_state
        end
    in
    let after_com_t1 = snd(raw_com_t1) in
    if (not(abt_one raw_com_t1)) then begin
      ref_state_list := after_com_t1::(!ref_state_list);
      if (check_raw_status raw_com_t1 != Non_exist) then begin
  	print_to_files state1 state2 after_com_t1 "comt1";
  	print_states_to_file after_com_t1
      end else ()
    end
    else begin
      let abt_t1_com_t1 = snd(abort_t1 (fst(after_com_t1)) (snd(after_com_t1))) in
      let abt_t2_com_t1 = snd(abort_t2 (fst(after_com_t1)) (snd(after_com_t1))) in
      ref_state_list :=  abt_t1_com_t1::(abt_t2_com_t1::(!ref_state_list));
      print_to_files state1 state2 after_com_t1 "comt1";
      print_states_to_file after_com_t1;
      print_to_files (fst(after_com_t1)) (snd(after_com_t1)) abt_t1_com_t1 "abtt1";
      print_states_to_file abt_t1_com_t1;
      print_to_files (fst(after_com_t1)) (snd(after_com_t1)) abt_t2_com_t1 "abtt2";
      print_states_to_file abt_t2_com_t1
    end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "comt1"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, com, t1") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)

  	  (* printf "No. %d: after_com_t1\n%s\n" (!state_no) (print_state_pair (fst(after_com_t1)) (snd(after_com_t1))); *)

  let after_com_t2_lst =
    let raw_com_t2 =
      try
  	Forward.find forward ((state1, state2), "tx, com, t2")
      with Not_found ->
  	let raw_post_state = commit_t2 state1 state2 in
  	match check_raw_status raw_post_state with
  	| Non_exist -> raw_post_state
  	| _ -> begin
  	    Forward.add forward ((state1, state2), "tx, com, t2") raw_post_state;
  	    raw_post_state
        end
    in
    let after_com_t2 = snd(raw_com_t2) in
    if (not(abt_one raw_com_t2)) then begin
      ref_state_list := after_com_t2::(!ref_state_list);
      if (check_raw_status raw_com_t2 != Non_exist) then begin
  	print_to_files state1 state2 after_com_t2 "comt2";
  	print_states_to_file after_com_t2
      end else ()
    end
    else begin
      let abt_t1_com_t2 = snd(abort_t1 (fst(after_com_t2)) (snd(after_com_t2))) in
      let abt_t2_com_t2 = snd(abort_t2 (fst(after_com_t2)) (snd(after_com_t2))) in
      ref_state_list := abt_t1_com_t2::(abt_t2_com_t2::(!ref_state_list));
      print_to_files state1 state2 after_com_t2 "comt2";
      print_states_to_file after_com_t2;
      print_to_files (fst(after_com_t2)) (snd(after_com_t2)) abt_t1_com_t2 "abtt1";
      print_states_to_file abt_t1_com_t2;
      print_to_files (fst(after_com_t2)) (snd(after_com_t2)) abt_t2_com_t2 "abtt2";
      print_states_to_file abt_t2_com_t2
    end
  in

      (* match check_status post_state 1 with *)
      (* |	Non_exist -> post_state *)
      (* |	_ -> begin *)
      (* 	  print_to_files state1 state2 post_state "comt2"; *)
      (* 	  Forward.add forward ((state1, state2), "tx, com, t2") post_state; *)
      (* 	  print_states_to_file post_state; *)
      (* 	  post_state *)
      (*   end *)

  	  (* printf "No. %d: after_com_t2\n%s\n" (!state_no) (print_state_pair (fst(after_com_t2)) (snd(after_com_t2))); *)

  (*** ZYY: nrd_t1_v1 doesn't need to be added into ref_state_list since it is not a final state ***)
  let nrd_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v1")
    with Not_found ->
      let post_state = nread_t1_v1 V1 state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
  	  print_to_files state1 state2 st "rdt1v1";
  	  Forward.add forward ((state1, state2), "nt, rd, t1, v1") post_state;
  	  print_states_to_file st;
  	  post_state
        end
  in
  	  (* printf "No. %d: nrd_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(nrd_t1_v1)) (snd(nrd_t1_v1))); *)

  let after_nread_t1_v1 =
    if (check_raw_status nrd_t1_v1) = Non_exist then ()
  	(* ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
    else begin
      let st = snd(nrd_t1_v1) in
      let st1 = fst(st) in
      let st2 = snd(st) in
      let raw_com_nread_t1_v1 =
	try
  	  Forward.find forward ((st1, st2), "nt, com, t1")
	with Not_found ->
  	  let post_state = ncommit_t1 st1 st2 in
  	  match check_raw_status post_state  with
  	  | Non_exist -> post_state
  	  | _ -> begin
  	      (* print_to_files st1 st2 post_state "comt1"; *)
  	      Forward.add forward ((st1, st2), "nt, com, t1") post_state;
  	      (* print_states_to_file post_state; *)
  	      post_state
          end
      in
      if check_raw_status raw_com_nread_t1_v1 = Non_exist then ()
      else begin
	let com_nread_t1_v1 = snd(raw_com_nread_t1_v1) in
	ref_state_list := com_nread_t1_v1::(!ref_state_list);
	print_to_files st1 st2 com_nread_t1_v1 "comt1";
	print_states_to_file com_nread_t1_v1
      end
    end
  in
  	  (* printf "No. %d: after_nread_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t1_v1)) (snd(after_nread_t1_v1))); *)

  let nrd_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v2")
    with Not_found ->
      let post_state = nread_t1_v2 V2 state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
  	  print_to_files state1 state2 st "rdt1v2";
  	  Forward.add forward ((state1, state2), "nt, rd, t1, v2") post_state;
  	  print_states_to_file st;
  	  post_state
        end
  in
  	  (* printf "No. %d: nrd_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(nrd_t1_v2)) (snd(nrd_t1_v2))); *)

  let after_nread_t1_v2 =
    if (check_raw_status nrd_t1_v2) = Non_exist then ()
  	(* ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
    else begin
      let st = snd(nrd_t1_v2) in
      let st1 = fst(st) in
      let st2 = snd(st) in
      let raw_com_nread_t1_v2 =
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
      if check_raw_status raw_com_nread_t1_v2 = Non_exist then ()
      else begin
	let com_nread_t1_v2 = snd(raw_com_nread_t1_v2) in
	ref_state_list := com_nread_t1_v2::(!ref_state_list);
	print_to_files st1 st2 com_nread_t1_v2 "comt1";
	print_states_to_file com_nread_t1_v2
      end
    end
  in
  	  (* printf "No. %d: after_nread_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t1_v2)) (snd(after_nread_t1_v2))); *)

  let nrd_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v1")
    with Not_found ->
      let post_state = nread_t2_v1 V1 state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
  	  print_to_files state1 state2 st "rdt2v1";
  	  Forward.add forward ((state1, state2), "nt, rd, t2, v1") post_state;
  	  print_states_to_file st;
  	  post_state
        end
  in
  	  (* printf "No. %d: nrd_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(nrd_t2_v1)) (snd(nrd_t2_v1))); *)

  let after_nread_t2_v1 =
    if (check_raw_status nrd_t2_v1 ) = Non_exist then ()
  	(* ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
    else begin
      let st = snd(nrd_t2_v1) in
      let st1 = fst(st) in
      let st2 = snd(st) in
      let raw_com_nread_t2_v1 =
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
      if check_raw_status raw_com_nread_t2_v1 = Non_exist then ()
      else begin
	let com_nread_t2_v1 = snd(raw_com_nread_t2_v1) in
	ref_state_list := com_nread_t2_v1::(!ref_state_list);
	print_to_files st1 st2 com_nread_t2_v1 "comt2";
	print_states_to_file com_nread_t2_v1
      end
    end
  in
  	  (* printf "No. %d: after_nread_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t2_v1)) (snd(after_nread_t2_v1))); *)

  let nrd_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v2")
    with Not_found ->
      let post_state = nread_t2_v1 V2 state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
  	  print_to_files state1 state2 st "rdt2v2";
  	  Forward.add forward ((state1, state2), "nt, rd, t2, v2") post_state;
  	  print_states_to_file st;
  	  post_state
        end
  in
  	  (* printf "No. %d: nrd_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(nrd_t2_v2)) (snd(nrd_t2_v2))); *)

  let after_nread_t2_v2 =
    if (check_raw_status nrd_t2_v2) = Non_exist then ()
  	(* ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
    else begin
      let st = snd(nrd_t2_v2) in
      let st1 = fst(st) in
      let st2 = snd(st) in
      let raw_com_nread_t2_v2 =
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
      if check_raw_status raw_com_nread_t2_v2 = Non_exist then ()
      else begin
	let com_nread_t2_v2 = snd(raw_com_nread_t2_v2) in
	ref_state_list := com_nread_t2_v2::(!ref_state_list);
	print_to_files st1 st2 com_nread_t2_v2 "comt2";
	print_states_to_file com_nread_t2_v2
      end
    end
  in
  	  (* printf "No. %d: after_nread_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nread_t2_v2)) (snd(after_nread_t2_v2))); *)

  let nwr_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v1")
    with Not_found ->
      let post_state = nwrite_t1_v1 V1 state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
  	  print_to_files state1 state2 st "wrt1v1";
  	  Forward.add forward ((state1, state2), "nt, wr, t1, v1") post_state;
  	  print_states_to_file st;
  	  post_state
        end
  in
  	  (* printf "No. %d: nwr_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(nwr_t1_v1)) (snd(nwr_t1_v1))); *)

  
  let after_nwrite_t1_v1 =
    if (check_raw_status nwr_t1_v1) = Non_exist then ()
  	(* ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
    else begin
      let st = snd (nwr_t1_v1) in
      let st1 = fst(st) in
      let st2 = snd(st) in
      let raw_com_write_t1_v1 =
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
      if check_raw_status raw_com_write_t1_v1 = Non_exist then ()
      else begin
	let com_write_t1_v1 = snd(raw_com_write_t1_v1) in
	ref_state_list := com_write_t1_v1::(!ref_state_list);
	print_to_files st1 st2 com_write_t1_v1 "comt1";
	print_states_to_file com_write_t1_v1
      end
    end
  in
  	  (* printf "No. %d: after_nwrite_t1_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t1_v1)) (snd(after_nwrite_t1_v1))); *)

  let nwr_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v2")
    with Not_found ->
      let post_state = nwrite_t1_v2 V2 state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
  	  print_to_files state1 state2 st "wrt1v2";
  	  Forward.add forward ((state1, state2), "nt, wr, t1, v2") post_state;
  	  print_states_to_file st;
  	  post_state
        end
  in
  	  (* printf "No. %d: nwr_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(nwr_t1_v2)) (snd(nwr_t1_v2))); *)

  let after_nwrite_t1_v2 =
    if (check_raw_status nwr_t1_v2) = Non_exist then ()
  	(* ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
    else begin
      let st = snd(nwr_t1_v2) in
      let st1 = fst(st) in
      let st2 = snd(st) in
      let raw_com_write_t1_v2 =
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
      if check_raw_status raw_com_write_t1_v2 = Non_exist then ()
      else begin
	let com_write_t1_v2 = snd(raw_com_write_t1_v2) in
	ref_state_list := com_write_t1_v2::(!ref_state_list);
	print_to_files st1 st2 com_write_t1_v2 "comt1";
	print_states_to_file com_write_t1_v2
      end
    end
  in
  	  (* printf "No. %d: after_nwrite_t1_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t1_v2)) (snd(after_nwrite_t1_v2))); *)

  let nwr_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v1")
    with Not_found ->
      let post_state = nwrite_t2_v1 V1 state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
  	  print_to_files state1 state2 st "wrt2v1";
  	  Forward.add forward ((state1, state2), "nt, wr, t2, v1") post_state;
  	  print_states_to_file st;
  	  post_state
        end
  in
  	  (* printf "No. %d: nwr_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(nwr_t2_v1)) (snd(nwr_t2_v1))); *)

  let after_nwrite_t2_v1 =
    if (check_raw_status nwr_t2_v1) = Non_exist then ()
  	(* ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
    else begin
      let st = snd(nwr_t2_v1) in
      let st1 = fst(st) in
      let st2 = snd(st) in
      let raw_com_write_t2_v1 =
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
      if check_raw_status raw_com_write_t2_v1 = Non_exist then ()
      else begin
	let com_write_t2_v1 = snd(raw_com_write_t2_v1) in
	ref_state_list := com_write_t2_v1::(!ref_state_list);
	print_to_files st1 st2 com_write_t2_v1 "comt2";
	print_states_to_file com_write_t2_v1
      end
    end
  in
  	  (* printf "No. %d: after_nwrite_t2_v1\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t2_v1)) (snd(after_nwrite_t2_v1))); *)

  let nwr_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v2")
    with Not_found ->
      let post_state = nwrite_t2_v2 V2 state1 state2 in
      match check_raw_status post_state with
      |	Non_exist -> post_state
      |	_ -> begin
	  let st = snd(post_state) in
  	  print_to_files state1 state2 st "wrt2v2";
  	  Forward.add forward ((state1, state2), "nt, wr, t2, v2") post_state;
  	  print_states_to_file st;
  	  post_state
        end
  in
  	  (* printf "No. %d: nwr_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(nwr_t2_v2)) (snd(nwr_t2_v2))); *)

  let after_nwrite_t2_v2 =
    if (check_raw_status nwr_t2_v2) = Non_exist then ()
  	(* ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I))) *)
    else begin
      let st = snd(nwr_t2_v2) in
      let st1 = fst(st) in
      let st2 = snd(st) in
      let raw_com_write_t2_v2 =
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
      if check_raw_status raw_com_write_t2_v2 = Non_exist then ()
      else begin
	let com_write_t2_v2 = snd(raw_com_write_t2_v2) in
	ref_state_list := com_write_t2_v2::(!ref_state_list);
	print_to_files st1 st2 com_write_t2_v2 "comt2";
	print_states_to_file com_write_t2_v2
      end
    end
  in
  	  (* printf "No. %d: after_nwrite_t2_v2\n%s\n" (!state_no) (print_state_pair (fst(after_nwrite_t2_v2)) (snd(after_nwrite_t2_v2))); *)

  (* let state_list = [after_tread_t1_v1(\* ; after_tread_t1_v2; after_tread_t2_v1; after_tread_t2_v2; after_twrite_t1_v1; after_twrite_t1_v2; after_twrite_t2_v1; after_twrite_t2_v2; *\) *)
  (* 		    (\* (\\* after_abt_t1; after_abt_t2; *\\) after_com_t1; after_com_t2; after_nread_t1_v1; after_nread_t1_v2; after_nread_t2_v1; after_nread_t2_v2; after_nwrite_t1_v1; *\) *)
  (* 		    (\* after_nwrite_t1_v2; after_nwrite_t2_v1; after_nwrite_t2_v2; *\) *)
  (* 		   ] in *)

(*** ZYY: all the after-functions need to be run before (!ref_state_list) is fetched ***)

after_tread_t1_v1_lst; after_tread_t1_v2_lst; after_tread_t2_v1_lst; after_tread_t2_v2_lst; after_twrite_t1_v1_lst; after_twrite_t1_v2_lst; after_twrite_t2_v1_lst; after_twrite_t2_v2_lst; after_com_t1_lst; after_com_t2_lst;
after_nread_t1_v1; after_nread_t1_v2; after_nread_t2_v1; after_nread_t2_v2; after_nwrite_t1_v1; after_nwrite_t1_v2; after_nwrite_t2_v1; after_nwrite_t2_v2;

  let stateSet = StateSet.empty in
  let newStateSet = List.fold_left (fun acc st -> StateSet.add st acc) stateSet (!ref_state_list) in
  let finalSet = StateSet.remove
      ((Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)), (Non_exist, 0, (None, None), (None, None), (None, None), (None, None), (None, None), (I, I)))
      newStateSet in
  let newList = StateSet.elements finalSet in
  
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
		    print_to_files (fst(st)) (snd(st)) aborted_st "abtt1";
		    print_states_to_file st;
		    print_states_to_file aborted_st;
		    Forward.add forward (st, "tx, abt, t1") tagged_st ;
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
	    	    print_to_files (fst(st)) (snd(st)) naborted_st "abtt1";
	    	    print_states_to_file st;
	    	    print_states_to_file naborted_st;
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
		    print_to_files (fst(st)) (snd(st)) aborted_st "abtt2";
		    print_states_to_file st;
		    print_states_to_file aborted_st;
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
	    	    print_to_files (fst(st)) (snd(st)) naborted_st "abtt2";
	    	    print_states_to_file st;
	    	    print_states_to_file naborted_st;
	    	    Forward.add forward (st, "nt, abt, t2") tagged_st;
	    	    tagged_st
		in
		snd(raw_inv)
	      end
	  end
	| _, _ -> st
	in proc_st::acc end) [] newList
      in
  (* ref_loop := (!ref_loop) + 1; *)
  (* printf "loop %d: \n" (!ref_loop); *)

(****************************Beginning of the debugging code********************************)
(* let rec print_state_file stateList acc =  *)
(*   match stateList with *)
(*   | [] -> acc *)
(*   | hd::tl -> begin *)
(*       let hd_str = print_state_pair (fst(hd)) (snd(hd)) in *)
(*       let pol_hd = polish_state "" hd_str in *)
(*       printf "The newList: %s\n" pol_hd; *)
(*       print_state_file tl acc *)
(*   end *)
(* in *)

(* print_state_file newList []; *)

(****************************End of the debugging code********************************)

(*   (\* printf "The post states of %s are:\n" (print_state_pair state1 state2); *\) *)
(*   (\* List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) finalList; *\) *)
(*   (\* printf "\n"; *\) *)
  finalList
end

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

print_state_file visited o_f;;
(* print_state_file visited o_s;; *)
close_out o_s;;
close_out o_t;;

(*let w_file = "../../huml-new/new_read_eager_TMESI_two_cache_line.ml"*)
let w_file = "new_read_eager_TMESI_two_cache_line.ml"
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


(* (\* (\\********** THE BEGINNING OF THE TESTING CODING **********\\) *\) *)
(* (\* let rec run_word word_list state_pair = begin *\) *)
(* (\*   match word_list with *\) *)
(* (\*   | [] -> state_pair *\) *)
(* (\*   | hd::tl -> *\) *)
(* (\*       let post_state = *\) *)
(* (\* 	match hd with *\) *)
(* (\* 	| "tx, rd, t1, v1" -> tread_t1 V1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, rd, t1, v2" -> tread_t1 V2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, rd, t2, v1" -> tread_t2 V1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, rd, t2, v2" -> tread_t2 V2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, wr, t1, v1" -> twrite_t1 V1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, wr, t1, v2" -> twrite_t1 V2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, wr, t2, v1" -> twrite_t2 V1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, wr, t2, v2" -> twrite_t2 V2 (fst(state_pair)) (snd(state_pair)) *\) *)

(* (\* 	| "tx, abt, t1" -> abort_t1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, abt, t2" -> abort_t2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, com, t1" -> commit_t1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "tx, com, t2" -> commit_t2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, rd, t1, v1" -> nread_t1 V1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, rd, t1, v2" -> nread_t1 V2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, rd, t2, v1" -> nread_t2 V1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, rd, t2, v2" -> nread_t2 V2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, wr, t1, v1" -> nwrite_t1 V1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, wr, t1, v2" -> nwrite_t1 V2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, wr, t2, v1" -> nwrite_t2 V1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, wr, t2, v2" -> nwrite_t2 V2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, abt, t1" -> nabort_t1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, abt, t2" -> nabort_t2 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| "nt, com, t1" -> ncommit_t1 (fst(state_pair)) (snd(state_pair)) *\) *)
(* (\* 	| _ -> ncommit_t2 (fst(state_pair)) (snd(state_pair)) (\\* i.e., "nt, com, t2" *\\) *\) *)
(* (\*       in *\) *)
(* (\*       run_word tl post_state *\) *)
(* (\* end *\) *)

(* (\* let pre_st = ((Active, 2, (None, None), (None, None), (None, None), (None, None), (None, None), M), (Invalid, 0, (None, None), (None, None), (None, None), (None, None), (None, None), I));; *\) *)
(* (\* let word_result = run_word ["tx, rd, t1, v1"; "tx, rd, t1, v2"; "tx, rd, t2, v1"; "tx, rd, t2, v2"; *\) *)
(* (\* 			    "tx, wr, t1, v1"; "tx, rd, t1, v2"; "tx, rd, t1, v1"; "tx, rd, t1, v2";(\\* "tx, rd, t2, v1"; "tx, rd, t1, v1"; *\\) *\) *)
(* (\* 			    "tx, com, t1"; (\\* "tx, abt, t2" "tx, rd, t2, v1"; "tx, rd, t2, v2"; "tx, com, t1" *\\)] init_state_pair *\) *)
(* (\* let word_result_str = print_state_pair (fst(word_result)) (snd(word_result));; *\) *)
(* (\* printf "The result of running a word is:\n %s\n" word_result_str;; *\) *)

(* (\* let inv_st = ((Committed, 0, (None, None), (None, None), (None, None), (None, None), (None, None), M), (Invalid, 0, (None, None), (None, None), (None, None), (None, None), (None, None), I));; *\) *)
(* (\* let abt_inv = abort_t2 (fst(inv_st)) (snd(inv_st));; *\) *)
(* (\* let abt_inv_str = print_state_pair (fst(abt_inv)) (snd(abt_inv));; *\) *)
(* (\* printf "The result of the aborted invalid state is:\n %s\n" abt_inv_str;; *\) *)
(* (\* (\\********** THE END OF THE TESTING CODING **********\\) *\) *)
 

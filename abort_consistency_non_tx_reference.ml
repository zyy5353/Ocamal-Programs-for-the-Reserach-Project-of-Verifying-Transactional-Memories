(* reference automaton with non-tx instructions which satisfies abort consistency*)

open Printf

type status =  Started | Invalid | Serialized | Finished | Non_exist
(* type trans = LRead | GRead | Write | Serialize | Commit | Abort *)
type var = V1 | V2
type thread = T1 | T2
type flag = int
type non_tx = int
type readSet = var option * var option
type writeSet = var option * var option
type prohReadSet = var option * var option
type prohWriteSet = var option * var option
type preds = thread option

type state = status * flag * non_tx * readSet * writeSet * prohReadSet * prohWriteSet * preds
type statePair = state * state

(*** TODO: compare the output automaton which only has gl_rd_t1_v1&2 after removing ser with that before removing ser ***)
(*** TODO: add the store_no and test if the number of the states is the same as visited states ***)
(*** TODO: make sure there is abort after each state except for the committed states ***)
(*** TODO: compare the abort-related paths with those in the TMESI automaton and make sure they are the same ***)
(*** TODO: recalculate the number of the states ***)
(*** TODO: add the comments to the program ***)

let status_to_string = function | Started -> "started" | Invalid -> "invalid" | Serialized -> "serialized" | Finished -> "finished" | Non_exist -> "non_exist"
let var_to_string = function | None -> "n" | Some V1 -> "v1" | Some V2 -> "v2" 
let thread_to_string = function | None -> "n" | Some T1 -> "t1" | Some T2 -> "t2" 
let flag_to_string = string_of_int
let non_tx_to_string = string_of_int
let print_wrSet (v1, v2) = "(" ^ var_to_string v1 ^ ", " ^ var_to_string v2 ^ ")" 
let print_preds t =  "(" ^ thread_to_string t ^ ") " 

let print_state ((sta, flg, non_tx, rs, ws, prs, pws, preds): state) = begin
  let sta_s = status_to_string sta in
  let flg_s = flag_to_string flg in
  let non_tx_s = non_tx_to_string non_tx in
  let rs_s = print_wrSet rs in
  let ws_s = print_wrSet ws in
  let prs_s = print_wrSet prs in
  let pws_s = print_wrSet pws in
  let preds_s = print_preds preds in
  sta_s^flg_s^non_tx_s^rs_s^ws_s^prs_s^pws_s^preds_s
end

let print_state_pair state1 state2 = begin
  let s1 = print_state state1 in
  let s2 = print_state state2 in
 s1^s2
end

let var_in_set (v: var)  wr_set = begin
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

let if_inter wr_set1 wr_set2 = begin
  match wr_set1, wr_set2 with
  | (Some V1, _), (Some V1, _) -> true
  | (_, Some V2), (_, Some V2) -> true
  | (_, _), (_, _) -> false
end

let merge_wr_set wr_set1 wr_set2 = begin
  let fst_v = match fst(wr_set1), fst(wr_set2) with
    | Some V1, _ -> Some V1
    | _, Some V1 -> Some V1
    | _, _ -> None
  in

  let snd_v = match snd(wr_set1), snd(wr_set2) with
    | Some V2, _ -> Some V2
    | _, Some V2 -> Some V2
    | _, _ -> None
  in
  (fst_v, snd_v)
end

(* A state in invalid status can also read or write but cannot serialize so it cannot commit *)
let local_read_t1 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    match var_in_set v ws1 with
    | true -> ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
    | false -> ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  end
end

let local_read_t2 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    match var_in_set v ws2 with
    | true -> ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
    | false -> ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  end
end

let global_read_t1 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    match var_in_set v ws1 with
    | true -> ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
    | false -> begin
	if sta1 = Invalid then ((Invalid, flg1, 0, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	else begin
	  match var_in_set v prs1 with
	  | true -> ((Invalid, flg1, 0, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	  | false -> begin
	      let rs = add_var v rs1 in
	      let sta = 
		match sta1 with
		| Finished -> Started
		| _ -> sta1
	      in
	      if (sta2 = Serialized && preds2 = None) then begin
		if (var_in_set v ws2) then ((sta, flg1, non_tx1, rs, ws1, prs1, pws1, preds1), (Invalid, flg2, 0, rs2, ws2, prs2, pws2, preds2))
		else let pws = add_var v pws2 in ((sta, flg1, non_tx1, rs, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws, preds2))
	      end
	      else ((sta, flg1, non_tx1, rs, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	  end
	end
	
        (* let sta = *)
	(*   match sta1 with *)
	(*   |  Finished -> Started *)
	(*   |  Serialized -> if var_in_set v prs1 then Invalid else Serialized *)
	(*   |  _ -> sta1 *)
	(* in *)
	
	(* match sta with *)
	(* | Invalid -> ((Invalid, flg1, 0, (None, None), (None, None), (None, None), (None, None), None), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2)) *)
	(* | _ -> begin *)
	(*     let rs = add_var v rs1 in *)
	(*     ((sta, flg1, non_tx1, rs, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2)) *)
	(* end *)
    end
  end
end

let global_read_t2 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    match var_in_set v ws2 with
    | true -> ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
    | false -> begin
	if sta2 = Invalid then ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, 0, rs2, ws2, prs2, pws2, preds2))
	else begin
	  match var_in_set v prs2 with
	  | true -> ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, 0, rs2, ws2, prs2, pws2, preds2))
	  | false -> begin
	      let rs = add_var v rs2 in
	      let sta = 
		match sta2 with
		| Finished -> Started
		| _ -> sta2
	      in
	      if (sta1 = Serialized && preds1 = None) then begin
		if (var_in_set v ws1) then ((Invalid, flg1, 0, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs, ws2, prs2, pws2, preds2))
		else let pws = add_var v pws1 in ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws, preds1), (sta, flg2, non_tx2, rs, ws2, prs2, pws2, preds2))
	      end
	      else ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs, ws2, prs2, pws2, preds2))
	  end
	end
	      
        (* let sta = *)
	(*   match sta2 with *)
	(*   |  Finished -> Started *)
	(*   |  Serialized -> if var_in_set v prs2 then Invalid else Serialized *)
	(*   |  _ -> sta2 *)
	(* in *)
	
	(* match sta with *)
	(* | Invalid -> ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, 0, (None, None), (None, None), (None, None), (None, None), None)) *)
	(* | _ -> begin *)
	(*     let rs = add_var v rs2 in *)
	(*     ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs, ws2, prs2, pws2, preds2)) *)
	(* end *)
    end
  end
end

let write_t1 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let sta =
      match sta1 with
      |  Finished -> Started
      |  Serialized -> if var_in_set v pws1 then Invalid else Serialized
      |  _ -> sta1
    in
    let ws = add_var v ws1 in
    ((sta, flg1, non_tx1, rs1, ws, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
    
    (* match sta with *)
    (* | Invalid -> ((Invalid, flg1, 0, (None, None), (None, None), (None, None), (None, None), None), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2)) *)
    (* | _ -> begin *)
    (* 	let ws = add_var v ws1 in *)
    (* 	((sta, flg1, non_tx1, rs1, ws, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2)) *)
    (* end *)
  end
end

let write_t2 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let sta =
      match sta2 with
      |  Finished -> Started
      |  Serialized -> if var_in_set v pws2 then Invalid else Serialized
      |  _ -> sta2
    in
    let ws = add_var v ws2 in
    ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs2, ws, prs2, pws2, preds2))
    
    (* match sta with *)
    (* | Invalid -> ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, 0, (None, None), (None, None), (None, None), (None, None), None)) *)
    (* | _ -> begin *)
    (* 	let ws = add_var v ws2 in *)
    (* 	((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs2, ws, prs2, pws2, preds2)) *)
    (* end *)
  end
end

let serialize_t1 ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if ((sta1 != Started) || ((non_tx1 != 0) || (non_tx2 != 0))) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let sta = Serialized in
    let flg = 1 in
    match sta2 with
    | Started -> begin
	match if_inter ws1 rs2 with
	| true -> ((Invalid, flg, 0, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	| false -> begin
	    let pws = merge_wr_set pws1 rs2 in
	    ((sta, flg, non_tx1, rs1, ws1, prs1, pws, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	end
    end
    | Serialized -> begin
	let preds = Some T2 in
	match if_inter ws2 rs1 with
	| true -> ((sta, flg, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, 0, rs2, ws2, prs2, pws2, preds2))
	| false -> begin 
	    let pws = merge_wr_set pws2 rs1 in
	    ((sta, flg, non_tx1, rs1, ws1, prs1, pws1, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws, preds2))
	end
    end
    | _ -> ((sta, flg, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
    
    (* match sta1 with *)
    (* | Started -> begin *)
    (* 	let sta = Serialized in *)
    (* 	let preds = *)
    (* 	  match sta2 with *)
    (* 	  | Serialized -> Some T2 *)
    (* 	  | _ -> preds1 *)
    (* 	in *)
    (* 	let flg = 1 in *)
    (* 	((sta, flg, non_tx1, rs1, ws1, prs1, pws1, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2)) *)
    (* end *)
    (* | _ -> ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None)) *)
  end
end

let serialize_t2 ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if ((sta2 != Started) || ((non_tx1 != 0) || (non_tx2 != 0))) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let sta = Serialized in
    let flg = 1 in
    match sta1 with
    | Started -> begin
	match if_inter ws2 rs1 with
	| true -> ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg, 0, rs2, ws2, prs2, pws2, preds2))
	| false -> begin
	    let pws = merge_wr_set pws2 rs1 in
	    ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg, non_tx2, rs2, ws2, prs2, pws, preds2))
	end
    end
    | Serialized -> begin
	let preds = Some T1 in
	match if_inter ws1 rs2 with
	| true -> ((Invalid, flg1, 0, rs1, ws1, prs1, pws1, preds1), (sta, flg, non_tx2, rs2, ws2, prs2, pws2, preds2))
	| false -> begin
	    let pws = merge_wr_set pws1 rs2 in
	    ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws, preds1), (sta, flg, non_tx2, rs2, ws2, prs2, pws2, preds))
	end
    end
    | _ -> ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg, non_tx2, rs2, ws2, prs2, pws2, preds2))
    
    (* match sta2 with *)
    (* | Started -> begin *)
    (* 	let sta = Serialized in *)
    (* 	let preds = *)
    (* 	  match sta1 with *)
    (* 	  | Serialized -> Some T1 *)
    (* 	  | _ -> preds2 *)
    (* 	in *)
    (* 	let flg = 1 in *)
    (*   ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg, non_tx2, rs2, ws2, prs2, pws2, preds)) *)
    (* end *)
    (* | _ -> ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None)) *)
  end
end

(*** TODO: need to set the output flag as 0? ***)
let commit_t1 ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    if sta1 = Finished || sta1 = Serialized then begin
      let sta = Finished in
      let rs = (None, None) in
      let ws = (None, None) in
      let prs = (None, None) in
      let pws = (None, None) in
      let preds = None in
      if ((sta2 = Finished) || (sta2 = Invalid)) then ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
      else begin
	match preds1 with
	| Some T2 -> begin
	  let prs2' = merge_wr_set prs2 ws1 in
	  let pws2' = merge_wr_set (merge_wr_set pws2 rs1) ws1 in
	  if (if_inter ws1 ws2) || (if_inter ws2 rs1) then ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (Invalid, flg2, 0, rs2, ws2, prs2', pws2', preds2))
	  else ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2', pws2', preds2))
	end
	| _ -> if if_inter ws1 rs2 then ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (Invalid, flg2, 0, rs2, ws2, prs2, pws2, preds2))
	else ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	    
	(* match preds1 with *)
	(* | Some T2 -> if (if_inter ws1 ws2) || (if_inter ws2 rs1) then ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (Invalid, flg2, 0, rs, ws, prs, pws, preds)) *)
	(* else begin *)
	(*   let prs2' = merge_wr_set prs2 ws1 in *)
	(*   let pws2' = merge_wr_set (merge_wr_set pws2 rs1) ws1 in *)
	(*   ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2', pws2', preds2)) *)
	(* end *)
	(* | _ -> if if_inter ws1 rs2 then ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (Invalid, flg2, 0, rs, ws, prs, pws, preds)) *)
	(* else ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2)) *)
      end
    end
    else ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  end
end

let commit_t2 ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    if sta2 = Finished || sta2 = Serialized then begin
      let sta = Finished in
      let rs = (None, None) in
      let ws = (None, None) in
      let prs = (None, None) in
      let pws = (None, None) in
      let preds = None in
      if ((sta1 = Finished) || (sta1 = Invalid)) then ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs, ws, prs, pws, preds)) 
      else begin
	match preds2 with
	| Some T1 -> begin
	  let prs1' = merge_wr_set prs1 ws2 in
	  let pws1' = merge_wr_set (merge_wr_set pws1 rs2) ws2 in
	  if (if_inter ws1 ws2) || (if_inter ws1 rs2) then ((Invalid, flg1, 0, rs1, ws1, prs1', pws1', preds1), (sta, flg2, non_tx2, rs, ws, prs, pws, preds))
	  else ((sta1, flg1, non_tx1, rs1, ws1, prs1', pws1', preds1), (sta, flg2, non_tx2, rs, ws, prs, pws, preds))
	end
	| _ -> if if_inter ws2 rs1 then ((Invalid, flg1, 0, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs, ws, prs, pws, preds))
	else ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs, ws, prs, pws, preds))
	
	(* match preds2 with *)
	(* | Some T1 -> if (if_inter ws1 ws2) || (if_inter ws1 rs2) then ((Invalid, flg1, 0, rs, ws, prs, pws, preds), (sta, flg2, non_tx2, rs, ws, prs, pws, preds)) *)
	(* else begin *)
	(*   let prs1' = merge_wr_set prs1 ws2 in *)
	(*   let pws1' = merge_wr_set (merge_wr_set pws1 rs2) ws2 in *)
	(*   ((sta1, flg1, non_tx1, rs1, ws1, prs1', pws1', preds1), (sta, flg2, non_tx2, rs, ws, prs, pws, preds)) *)
	(* end *)
	(* | _ -> if if_inter ws2 rs1 then ((Invalid, flg1, 0, rs, ws, prs, pws, preds), (sta, flg2, non_tx2, rs, ws, prs, pws, preds)) *)
	(* else ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs, ws, prs, pws, preds)) *)
      end
    end
    else ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  end
end

let abort_t1 ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) = begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let sta = Finished in
    let rs = (None, None) in
    let ws = (None, None) in
    let prs = (None, None) in
    let pws = (None, None) in
    let preds = None in
    ((sta, flg1, non_tx1, rs, ws, prs, pws, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
  end
end

let abort_t2  ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) = begin
  if (non_tx1 != 0) || (non_tx2 != 0) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let sta = Finished in
    let rs = (None, None) in
    let ws = (None, None) in
    let prs = (None, None) in
    let pws = (None, None) in
    let preds = None in
    ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx2, rs, ws, prs, pws, preds))
  end
end


let nread_t1 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (((sta1 != Finished) || (non_tx1 != 0)) || (non_tx2 != 0)) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let rs1' = add_var v rs1 in
    (* let non_tx = 0 in *)
    (* let rs = (None, None) in *)
    (* let ws = (None, None) in *)
    (* let prs = (None, None) in *)
    (* let pws = (None, None) in *)
    (* let preds = None in *)
    match sta2 with
    | Serialized -> begin 
	if (if_inter ws1 ws2) || (if_inter ws2 rs1') then ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	else begin
	  let prs2' = merge_wr_set prs2 ws1 in
	  let pws2' = merge_wr_set (merge_wr_set pws2 rs1') ws1 in
	    ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2', pws2', preds2))
	end
    end
    | _ -> begin 
	if if_inter ws1 rs2 then ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, 0, rs2, ws2, prs2, pws2, preds2))
	else ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
    end
  end
end

let nread_t2 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (((sta2 != Finished) || (non_tx1 != 0)) || (non_tx2 != 0)) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let rs2' = add_var v rs2 in
    (* let non_tx = 0 in *)
    (* let rs = (None, None) in *)
    (* let ws = (None, None) in *)
    (* let prs = (None, None) in *)
    (* let pws = (None, None) in *)
    (* let preds = None in *)
    match sta1 with
    | Serialized -> begin 
	if (if_inter ws1 ws2) || (if_inter ws1 rs2') then ((Invalid, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	else begin
	  let prs1' = merge_wr_set prs1 ws2 in
	  let pws1' = merge_wr_set (merge_wr_set pws1 rs2') ws2 in
	    ((sta1, flg1, non_tx1, rs1, ws1, prs1', pws1', preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	end
    end
    | _ -> begin 
	if if_inter ws2 rs1 then ((Invalid, flg1, 0, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	else ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
    end
  end
end

let nwrite_t1 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (((sta1 != Finished) || (non_tx1 != 0)) || (non_tx2 != 0)) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let ws1' = add_var v ws1 in
    (* let non_tx = 0 in *)
    (* let rs = (None, None) in *)
    (* let ws = (None, None) in *)
    (* let prs = (None, None) in *)
    (* let pws = (None, None) in *)
    (* let preds = None in *)
    match sta2 with
    | Serialized -> begin 
	if (if_inter ws1' ws2) || (if_inter ws2 rs1) then ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	else begin
	  let prs2' = merge_wr_set prs2 ws1' in
	  let pws2' = merge_wr_set (merge_wr_set pws2 rs1) ws1' in
	    ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2', pws2', preds2))
	end
    end
    | _ -> begin 
	if if_inter ws1' rs2 then ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (Invalid, flg2, 0, rs2, ws2, prs2, pws2, preds2))
	else ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
    end
  end
end

let nwrite_t2 (v: var) ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin
  if (((sta2 != Finished) || (non_tx1 != 0)) || (non_tx2 != 0)) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
  else begin
    let ws2' = add_var v ws2 in
    (* let non_tx = 0 in *)
    (* let rs = (None, None) in *)
    (* let ws = (None, None) in *)
    (* let prs = (None, None) in *)
    (* let pws = (None, None) in *)
    (* let preds = None in *)
    match sta1 with
    | Serialized -> begin 
	if (if_inter ws1 ws2') || (if_inter ws1 rs2) then ((Invalid, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	else begin
	  let prs1' = merge_wr_set prs1 ws2' in
	  let pws1' = merge_wr_set (merge_wr_set pws1 rs2) ws2' in
	    ((sta1, flg1, non_tx1, rs1, ws1, prs1', pws1', preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	end
    end
    | _ -> begin 
	if if_inter ws2' rs1 then ((Invalid, flg1, 0, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
	else ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2))
    end
  end
end

(* let ncommit_t1 ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin *)
(*   if (((sta1 != Started) || (non_tx1 != 1)) || (non_tx2 != 0)) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None)) *)
(*   else begin *)
(*       let sta = Finished in *)
(*       let non_tx = 0 in *)
(*       let rs = (None, None) in *)
(*       let ws = (None, None) in *)
(*       let prs = (None, None) in *)
(*       let pws = (None, None) in *)
(*       let preds = None in *)
(*       match sta2 with *)
(*       | Serialized -> if (if_inter ws1 ws2) || (if_inter ws2 rs1) then ((sta, flg1, non_tx, rs, ws, prs, pws, preds), (Invalid, flg2, 0, rs, ws, prs, pws, preds)) *)
(*       else begin *)
(* 	let prs2' = merge_wr_set prs2 ws1 in *)
(* 	let pws2' = merge_wr_set (merge_wr_set pws2 rs1) ws1 in *)
(* 	((sta, flg1, non_tx, rs, ws, prs, pws, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2', pws2', preds2)) *)
(*       end *)
(*       | _ -> begin if if_inter ws1 rs2 then ((sta, flg1, non_tx, rs, ws, prs, pws, preds), (Invalid, flg2, 0, rs, ws, prs, pws, preds)) *)
(*       else ((sta, flg1, non_tx, rs, ws, prs, pws, preds), (sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2)) *)
(*     end *)
(*   end *)
(* end *)

(* let ncommit_t2 ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) =  begin *)
(*   if (((sta2 != Started) || (non_tx1 != 0)) || (non_tx2 != 1)) then ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None)) *)
(*   else begin *)
(*       let sta = Finished in *)
(*       let non_tx = 0 in *)
(*       let rs = (None, None) in *)
(*       let ws = (None, None) in *)
(*       let prs = (None, None) in *)
(*       let pws = (None, None) in *)
(*       let preds = None in *)
(*       match sta2 with *)
(*       | Serialized -> if (if_inter ws1 ws2) || (if_inter ws1 rs2) then ((Invalid, flg1, 0, rs, ws, prs, pws, preds), (sta, flg2, non_tx, rs, ws, prs, pws, preds)) *)
(*       else begin *)
(* 	let prs1' = merge_wr_set prs1 ws2 in *)
(* 	let pws1' = merge_wr_set (merge_wr_set pws1 rs2) ws2 in *)
(* 	((sta1, flg1, non_tx1, rs1, ws1, prs1', pws1', preds1), (sta, flg2, non_tx, rs, ws, prs, pws, preds)) *)
(*       end *)
(*       | _ -> begin if if_inter ws2 rs1 then ((Invalid, flg1, 0, rs, ws, prs, pws, preds), (sta, flg2, non_tx, rs, ws, prs, pws, preds)) *)
(*       else ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta, flg2, non_tx, rs, ws, prs, pws, preds)) *)
(*     end *)
(*   end *)
(* end *)

(*** There is no need to have nabort functions here because the invalidated transactions will be aborted in the get_post_state function later on. ***) 
(*** The abort function is used to abort after any states except for the ones that are in a non-transactional instruction, that's why the abort function is needed ***) 

let zero_flg ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) = begin
  ((sta1, 0, non_tx1, rs1, ws1, prs1, pws1, preds1), (sta2, 0, non_tx2, rs2, ws2, prs2, pws2, preds2))
end

let get_status state = begin
  match state with
  | (sta, _, _, _, _, _, _, _) -> sta
end

let check_status state_pair i = begin
  match i with
  | 1 -> get_status (fst(state_pair))
  | _ -> get_status (snd(state_pair))
end;;

let get_flg ((sta, flg, non_tx, rs, ws, prs, pws, preds): state) = flg;;

let get_flgs ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) = (flg1, flg2);;

let if_flg1 ((sta1, flg1, non_tx1, rs1, ws1, prs1, pws1, preds1): state) ((sta2, flg2, non_tx2, rs2, ws2, prs2, pws2, preds2): state) = begin
  match flg1, flg2 with
  | 0, 0 -> false
  | _, _ -> true
end;;

module StateSet = Set.Make(struct type t = (state * state) let compare = Pervasives.compare end)
module Forward = Hashtbl.Make(struct
  type t = (state * state) * string
  let hash = Hashtbl.hash
  let equal = (=)
end)

(*** TODO: Backward talbe is not needed here because all the non-final states, which are invalid states, will be aborted right away in the reference automaton ***)
module Backward = Hashtbl.Make(struct
  type t = state * state
  let hash = Hashtbl.hash
  let equal = (=)
end)

module Ser_trans = Hashtbl.Make(struct
  type t = (state * state) * string
  let hash = Hashtbl.hash
  let equal = (=)
end)

(*let state1 = (Started, (None, None), (None, None), (None, None), (None, None), None);;*)
(*let state2 = (Started, (None, None), (None, None), (None, None), (None, None), None);;*)

let rec polish_state acc state_pair = begin
(*** TODO: if flg1 = 1 or flg2 = 1 then "" else like the following ***)
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

let init_state_pair = ((Finished, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Finished, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
let str_init = print_state_pair (fst(init_state_pair)) (snd(init_state_pair))
let p_init = polish_state "" str_init;;
(* let out = ref stdout *)
let t_file = "Transitions.ml"
let f_file = "Final_states.ml"
let s_file = "States.ml"
let o_t = open_out t_file;;
let o_f = open_out f_file;;
let o_s = open_out s_file;;
fprintf o_t "Transitions\ni -> %s\n" p_init;;
fprintf o_f "Final States\n";;
fprintf o_s "States\n";;
(* out := o_t *)

let print_to_files state1 state2 post str = begin
  let state_str = print_state_pair state1 state2 in
  let p_state_str = polish_state "" state_str in
  let post_str = print_state_pair (fst(post)) (snd(post)) in
  let p_post_str = polish_state "" post_str in
  let t_str = str^"("^p_state_str^")"^" -> "^p_post_str in
  (*let oc = open_out file in*)
  (*output_string oc t_str;*)
  fprintf o_t "%s\n" t_str
  (*close_out o_t*)
end

let print_states_to_file st = begin
  let st_str = print_state_pair (fst(st)) (snd(st)) in
  let pol_st = polish_state "" st_str in
  fprintf o_f "%s\n" pol_st;
  fprintf o_s "%s\n" pol_st;
end

type pre_state = {mutable preStates: (state * state) list} (* preStates is a mutable record *)
let forward : (state * state) Forward.t = Forward.create 0
let backward : pre_state Backward.t = Backward.create 0
let ser_trans : (state * state) Ser_trans.t = Ser_trans.create 0

let ref_loop = ref 0
let state_no = ref 0

(*** TODO: invoke the flg_zero function after a non-ser operation on a flg_1 state and then output the flg0 state ***)
let  get_post_state state1 state2 = begin
  (*** TODO: check the correctness of the whole function ***)
  let non_exist = ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None)) in
  (*let pre = {preStates = []} in*)

  let after_lc_rd_t1_v1 =
    try
      Forward.find forward ((state1, state2), "lc, rd, t1, v1")
    with Not_found ->
      let post_state = local_read_t1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt1v1";
  	      Forward.add forward ((state1, state2), "lc, rd, t1, v1") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v1";
  	      Forward.add forward ((state1, state2), "lc, rd, t1, v1") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v1";
  	      Forward.add forward ((state1, state2), "lc, rd, t1, v1") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      (*** TODO: why is the other case unused? ***)
  	      let pre = begin
  		(* match pre'' with  *)
  	        (* | non_exist -> begin *)
  		(*     let pre' =  *)
  		(*       try *)
  		(* 	Ser_trans.find ser_trans ((state1, state2), "ser, t1") *)
  		(*       with Not_found -> begin  *)
  		(* 	printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);	   *)
  		(* 	non_exist		     *)
  		(*       end *)
  		(*     in  *)
  		(*     try  *)
  		(*       Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2") *)
  		(*     with Not_found -> begin *)
  		(*       printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre'))); *)
  		(*       non_exist		   *)
  		(*       end *)
  		(*   end *)
  		(* | _ -> begin *)
  		(*     try *)
  		(*       Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1") *)
  		(*     with Not_found ->  begin  *)
  		(* 	printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));	   *)
  		(* 	non_exist		     *)
  		(*       end     *)
  		(*   end *)
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v1";
  	      Forward.add forward ((state1, state2), "lc, rd, t1, v1") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_lc_rd_t1_v2 =
    try
      Forward.find forward ((state1, state2), "lc, rd, t1, v2")
    with Not_found ->
      let post_state = local_read_t1 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
  	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt1v2";
  	      Forward.add forward ((state1, state2), "lc, rd, t1, v2") post_state;
  	      post_state
  	     end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v2";
  	      Forward.add forward ((state1, state2), "lc, rd, t1, v2") post_zero;
  	      post_zero
  	     end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v2";
  	      Forward.add forward ((state1, state2), "lc, rd, t1, v2") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v2";
  	      Forward.add forward ((state1, state2), "lc, rd, t1, v2") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_lc_rd_t2_v1 =
    try
      Forward.find forward ((state1, state2), "lc, rd, t2, v1")
    with Not_found ->
      let post_state = local_read_t2 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt2v1";
  	      Forward.add forward ((state1, state2), "lc, rd, t2, v1") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v1";
  	      Forward.add forward ((state1, state2), "lc, rd, t2, v1") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v1";
  	      Forward.add forward ((state1, state2), "lc, rd, t2, v1") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v1";
  	      Forward.add forward ((state1, state2), "lc, rd, t2, v1") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_lc_rd_t2_v2 =
    try
      Forward.find forward ((state1, state2), "lc, rd, t2, v2")
    with Not_found ->
      let post_state = local_read_t2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt2v2";
  	      Forward.add forward ((state1, state2), "lc, rd, t2, v2") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v2";
  	      Forward.add forward ((state1, state2), "lc, rd, t2, v2") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v2";
  	      Forward.add forward ((state1, state2), "lc, rd, t2, v2") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v2";
  	      Forward.add forward ((state1, state2), "lc, rd, t2, v2") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_gl_rd_t1_v1 =
    try
      Forward.find forward ((state1, state2), "gl, rd, t1, v1")
    with Not_found ->
      let post_state = global_read_t1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt1v1";
  	      Forward.add forward ((state1, state2), "gl, rd, t1, v1") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v1";
  	      Forward.add forward ((state1, state2), "gl, rd, t1, v1") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v1";
  	      Forward.add forward ((state1, state2), "gl, rd, t1, v1") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v1";
  	      Forward.add forward ((state1, state2), "gl, rd, t1, v1") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_gl_rd_t1_v2 =
    try
      Forward.find forward ((state1, state2), "gl, rd, t1, v2")
    with Not_found ->
      let post_state = global_read_t1 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt1v2";
  	      Forward.add forward ((state1, state2), "gl, rd, t1, v2") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v2";
  	      Forward.add forward ((state1, state2), "gl, rd, t1, v2") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v2";
  	      Forward.add forward ((state1, state2), "gl, rd, t1, v2") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt1v2";
  	      Forward.add forward ((state1, state2), "gl, rd, t1, v2") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_gl_rd_t2_v1 =
    try
      Forward.find forward ((state1, state2), "gl, rd, t2, v1")
    with Not_found ->
      let post_state = global_read_t2 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt2v1";
  	      Forward.add forward ((state1, state2), "gl, rd, t2, v1") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v1";
  	      Forward.add forward ((state1, state2), "gl, rd, t2, v1") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v1";
  	      Forward.add forward ((state1, state2), "gl, rd, t2, v1") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v1";
  	      Forward.add forward ((state1, state2), "gl, rd, t2, v1") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_gl_rd_t2_v2 =
    try
      Forward.find forward ((state1, state2), "gl, rd, t2, v2")
    with Not_found ->
      let post_state = global_read_t2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "rdt2v2";
  	      Forward.add forward ((state1, state2), "gl, rd, t2, v2") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v2";
  	      Forward.add forward ((state1, state2), "gl, rd, t2, v2") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v2";
  	      Forward.add forward ((state1, state2), "gl, rd, t2, v2") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "rdt2v2";
  	      Forward.add forward ((state1, state2), "gl, rd, t2, v2") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_wr_t1_v1 =
    try
      Forward.find forward ((state1, state2), "wr, t1, v1")
    with Not_found ->
      let post_state = write_t1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt1v1";
  	      Forward.add forward ((state1, state2), "wr, t1, v1") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt1v1";
  	      Forward.add forward ((state1, state2), "wr, t1, v1") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt1v1";
  	      Forward.add forward ((state1, state2), "wr, t1, v1") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt1v1";
  	      Forward.add forward ((state1, state2), "wr, t1, v1") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_wr_t1_v2 =
    try
      Forward.find forward ((state1, state2), "wr, t1, v2")
    with Not_found ->
      let post_state = write_t1 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt1v2";
  	      Forward.add forward ((state1, state2), "wr, t1, v2") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt1v2";
  	      Forward.add forward ((state1, state2), "wr, t1, v2") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt1v2";
  	      Forward.add forward ((state1, state2), "wr, t1, v2") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt1v2";
  	      Forward.add forward ((state1, state2), "wr, t1, v2") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_wr_t2_v1 =
    try
      Forward.find forward ((state1, state2), "wr, t2, v1")
    with Not_found ->
      let post_state = write_t2 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt2v1";
  	      Forward.add forward ((state1, state2), "wr, t2, v1") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt2v1";
  	      Forward.add forward ((state1, state2), "wr, t2, v1") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt2v1";
  	      Forward.add forward ((state1, state2), "wr, t2, v1") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt2v1";
  	      Forward.add forward ((state1, state2), "wr, t2, v1") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_wr_t2_v2 =
    try
      Forward.find forward ((state1, state2), "wr, t2, v2")
    with Not_found ->
      let post_state = write_t2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "wrt2v2";
  	      Forward.add forward ((state1, state2), "wr, t2, v2") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt2v2";
  	      Forward.add forward ((state1, state2), "wr, t2, v2") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt2v2";
  	      Forward.add forward ((state1, state2), "wr, t2, v2") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "wrt2v2";
  	      Forward.add forward ((state1, state2), "wr, t2, v2") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_ser_t1 =
    try
      Forward.find forward ((state1, state2), "ser, t1")
    with Not_found ->
      let post_state = serialize_t1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  (* print_to_files state1 state2 post_state "sert1"; *)
  	  Forward.add forward ((state1, state2), "ser, t1") post_state;
  	  Ser_trans.add ser_trans (post_state, "ser, t1") (state1, state2);
  	  post_state
        end
      in

  let after_ser_t2 =
    try
      Forward.find forward ((state1, state2), "ser, t2")
    with Not_found ->
      let post_state = serialize_t2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  (* print_to_files state1 state2 post_state "sert2"; *)
  	  Forward.add forward ((state1, state2), "ser, t2") post_state;
  	  Ser_trans.add ser_trans (post_state, "ser, t2") (state1, state2);
  	  post_state
        end
      in

  let after_com_t1 =
    try
      Forward.find forward ((state1, state2), "com, t1")
    with Not_found ->
      let post_state = commit_t1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "comt1";
  	      Forward.add forward ((state1, state2), "com, t1") post_state;
  	      post_state
            end
	  | (_, 0) -> begin
	      let pre =
		try
		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
		with Not_found -> non_exist
	      in
	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
	      print_to_files (fst(pre)) (snd(pre)) post_zero "comt1";
  	      Forward.add forward ((state1, state2), "com, t1") post_zero;
	      post_zero
	    end
	  | (0, _) -> begin
	      let pre =
		try
		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
		with Not_found -> non_exist
	      in
	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
	      print_to_files (fst(pre)) (snd(pre)) post_zero "comt1";
  	      Forward.add forward ((state1, state2), "com, t1") post_zero;
	      post_zero
	    end
	  | (_, _) -> begin
	      let pre'' =
		try
		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
		with Not_found -> non_exist
	      in
	      let pre = begin
		if (pre'' == non_exist) then begin
		    let pre' =
		      try
			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
		      with Not_found -> begin
			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
			non_exist
		      end
		    in
		    try
		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
		    with Not_found -> begin
		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
		      non_exist
		      end
		  end
		else begin
		    try
		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
		    with Not_found ->  begin
			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
			non_exist
		      end
		  end
	        end in
	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
	      print_to_files (fst(pre)) (snd(pre)) post_zero "comt1";
  	      Forward.add forward ((state1, state2), "comt1") post_zero;
	      post_zero
	    end
        end
      in

  let after_com_t2 =
    try
      Forward.find forward ((state1, state2), "com, t2")
    with Not_found ->
      let post_state = commit_t2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "comt2";
  	      Forward.add forward ((state1, state2), "com, t2") post_state;
  	      post_state
            end
	  | (_, 0) -> begin
	      let pre =
		try
		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
		with Not_found -> non_exist
	      in
	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
	      print_to_files (fst(pre)) (snd(pre)) post_zero "comt2";
  	      Forward.add forward ((state1, state2), "com, t2") post_zero;
	      post_zero
	    end
	  | (0, _) -> begin
	      let pre =
		try
		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
		with Not_found -> non_exist
	      in
	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
	      print_to_files (fst(pre)) (snd(pre)) post_zero "comt2";
  	      Forward.add forward ((state1, state2), "com, t2") post_zero;
	      post_zero
	    end
	  | (_, _) -> begin
	      let pre'' =
		try
		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
		with Not_found -> non_exist
	      in
	      let pre = begin
		if (pre'' == non_exist) then begin
		    let pre' =
		      try
			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
		      with Not_found -> begin
			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
			non_exist
		      end
		    in
		    try
		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
		    with Not_found -> begin
		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
		      non_exist
		      end
		  end
		else begin
		    try
		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
		    with Not_found ->  begin
			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
			non_exist
		      end
		  end
	        end in
	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
	      print_to_files (fst(pre)) (snd(pre)) post_zero "comt2";
  	      Forward.add forward ((state1, state2), "comt2") post_zero;
	      post_zero
	    end
         end
      in

  let after_abt_t1 =
    try
      Forward.find forward ((state1, state2), "abt, t1")
    with Not_found ->
      let post_state = abort_t1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "abtt1";
  	      Forward.add forward ((state1, state2), "abt, t1") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "abtt1";
  	      Forward.add forward ((state1, state2), "abt, t1") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "abtt1";
  	      Forward.add forward ((state1, state2), "abt, t1") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "abtt1";
  	      Forward.add forward ((state1, state2), "abtt1") post_zero;
  	      post_zero
  	    end
        end
      in

  let after_abt_t2 =
    try
      Forward.find forward ((state1, state2), "abt, t2")
    with Not_found ->
      let post_state = abort_t2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flgs state1 state2 with
       	  | (0, 0) -> begin
  	      print_to_files state1 state2 post_state "abtt2";
  	      Forward.add forward ((state1, state2), "abt, t2") post_state;
  	      post_state
            end
  	  | (_, 0) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "abtt2";
  	      Forward.add forward ((state1, state2), "abt, t2") post_zero;
  	      post_zero
  	    end
  	  | (0, _) -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "abtt2";
  	      Forward.add forward ((state1, state2), "abt, t2") post_zero;
  	      post_zero
  	    end
  	  | (_, _) -> begin
  	      let pre'' =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let pre = begin
  		if (pre'' == non_exist) then begin
  		    let pre' =
  		      try
  			Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		      with Not_found -> begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair state1 state2);
  			non_exist
  		      end
  		    in
  		    try
  		      Ser_trans.find ser_trans (((fst(pre')), (snd(pre'))), "ser, t2")
  		    with Not_found -> begin
  		      printf "The pre state of sert2 is not found: %s\n" (print_state_pair (fst(pre')) (snd(pre')));
  		      non_exist
  		      end
  		  end
  		else begin
  		    try
  		      Ser_trans.find ser_trans (((fst(pre'')), (snd(pre''))), "ser, t1")
  		    with Not_found ->  begin
  			printf "The pre state of sert1 is not found: %s\n" (print_state_pair (fst(pre'')) (snd(pre'')));
  			non_exist
  		      end
  		  end
  	        end in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "abtt2";
  	      Forward.add forward ((state1, state2), "abtt2") post_zero;
  	      post_zero
  	    end
         end
      in

  let after_nread_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v1")
    with Not_found ->
      let post_state = nread_t1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flg state2 with
       	  | 0 -> begin
  	      print_to_files state1 state2 post_state "nrdt1v1";
  	      Forward.add forward ((state1, state2), "nt, rd, t1, v1") post_state;
  	      (* print_states_to_file post_state; (\*** need to print out the states here since it will not be processed in finalList which prints out the state ***\) *)
  	      post_state
            end
  	  | _ -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "nrdt1v1";
  	      Forward.add forward ((state1, state2), "nt, rd, t1, v1") post_zero;
  	      (* print_states_to_file post_zero;  *)
  	      post_zero
  	  end
      end
  in

  (* let after_nread_t1_v1 = *)
  (*   if (check_status nrd_t1_v1 1) = Non_exist then non_exist *)
  (*   else begin *)
  (*     let st1 = fst(nrd_t1_v1) in *)
  (*     let st2 = snd(nrd_t1_v1) in *)
  (*     try *)
  (* 	Forward.find forward ((st1, st2), "nt, rd, t1") *)
  (*     with Not_found -> *)
  (* 	let post_state = ncommit_t1 st1 st2 in *)
  (* 	match check_status post_state 1 with *)
  (* 	| Non_exist -> post_state *)
  (* 	| _ -> begin *)
  (* 	    print_to_files st1 st2 post_state "comt1"; *)
  (* 	    Forward.add forward ((st1, st2), "nt, com, t1") post_state; *)
  (* 	    post_state *)
  (*         end *)
  (*   end *)
  (* in *)

  let after_nread_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t1, v2")
    with Not_found ->
      let post_state = nread_t1 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flg state2 with
  	  | 0 -> begin
  	      print_to_files state1 state2 post_state "nrdt1v2";
  	      Forward.add forward ((state1, state2), "nt, rd, t1, v2") post_state;
  	      (* print_states_to_file post_state; *)
  	      post_state
  	     end
  	  | _ -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "nrdt1v2";
  	      Forward.add forward ((state1, state2), "nt, rd, t1, v2") post_zero;
  	      (* print_states_to_file post_zero; *)
  	      post_zero
  	  end
      end
  in

  (* let after_nread_t1_v2 = *)
  (*   if (check_status nrd_t1_v2 1) = Non_exist then non_exist *)
  (*   else begin *)
  (*     let st1 = fst(nrd_t1_v2) in *)
  (*     let st2 = snd(nrd_t1_v2) in *)
  (*     try *)
  (* 	Forward.find forward ((st1, st2), "nt, com, t1") *)
  (*     with Not_found -> *)
  (* 	let post_state = ncommit_t1 st1 st2 in *)
  (* 	match check_status post_state 1 with *)
  (* 	| Non_exist -> post_state *)
  (* 	| _ -> begin *)
  (* 	    print_to_files st1 st2 post_state "comt1"; *)
  (* 	    Forward.add forward ((st1, st2), "nt, com, t1") post_state; *)
  (* 	    post_state *)
  (*         end *)
  (*   end *)
  (* in *)

  let after_nread_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v1")
    with Not_found ->
      let post_state = nread_t2 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flg state1 with
       	  | 0 -> begin
  	      print_to_files state1 state2 post_state "nrdt2v1";
  	      Forward.add forward ((state1, state2), "nt, rd, t2, v1") post_state;
  	      (* print_states_to_file post_state; *)
  	      post_state
            end
  	  | _ -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "nrdt2v1";
  	      Forward.add forward ((state1, state2), "nt, rd, t2, v1") post_zero;
  	      (* print_states_to_file post_zero; *)
  	      post_zero
  	  end
      end
  in

  (* let after_nread_t2_v1 = *)
  (*   if (check_status nrd_t2_v1 1) = Non_exist then non_exist *)
  (*   else begin *)
  (*     let st1 = fst(nrd_t2_v1) in *)
  (*     let st2 = snd(nrd_t2_v1) in *)
  (*     try *)
  (* 	Forward.find forward ((st1, st2), "nt, com, t2") *)
  (*     with Not_found -> *)
  (* 	let post_state = ncommit_t2 st1 st2 in *)
  (* 	match check_status post_state 1 with *)
  (* 	| Non_exist -> post_state *)
  (* 	| _ -> begin *)
  (* 	    print_to_files st1 st2 post_state "comt2"; *)
  (* 	    Forward.add forward ((st1, st2), "nt, com, t2") post_state; *)
  (* 	    post_state *)
  (*         end *)
  (*   end *)
  (* in *)

  let after_nread_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, rd, t2, v2")
    with Not_found ->
      let post_state = nread_t2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flg state1 with
       	  | 0 -> begin
  	      print_to_files state1 state2 post_state "nrdt2v2";
  	      Forward.add forward ((state1, state2), "nt, rd, t2, v2") post_state;
  	      (* print_states_to_file post_state; *)
  	      post_state
            end
  	  | _ -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "nrdt2v2";
  	      Forward.add forward ((state1, state2), "nt, rd, t2, v2") post_zero;
  	      (* print_states_to_file post_zero; *)
  	      post_zero
  	  end
      end
  in

  (* let after_nread_t2_v2 = *)
  (*   if (check_status nrd_t2_v2 1) = Non_exist then non_exist *)
  (*   else begin *)
  (*     let st1 = fst(nrd_t2_v2) in *)
  (*     let st2 = snd(nrd_t2_v2) in *)
  (*     try *)
  (* 	Forward.find forward ((st1, st2), "nt, com, t2") *)
  (*     with Not_found -> *)
  (* 	let post_state = ncommit_t2 st1 st2 in *)
  (* 	match check_status post_state 1 with *)
  (* 	| Non_exist -> post_state *)
  (* 	| _ -> begin *)
  (* 	    print_to_files st1 st2 post_state "comt2"; *)
  (* 	    Forward.add forward ((st1, st2), "nt, com, t2") post_state; *)
  (* 	    post_state *)
  (*         end *)
  (*   end *)
  (* in *)

  let after_nwrite_t1_v1 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v1")
    with Not_found ->
      let post_state = nwrite_t1 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flg state2 with
       	  | 0 -> begin
  	      print_to_files state1 state2 post_state "nwrt1v1";
  	      Forward.add forward ((state1, state2), "nt, wr, t1, v1") post_state;
  	      (* print_states_to_file post_state; *)
  	      post_state
            end
  	  | _ -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "nwrt1v1";
  	      Forward.add forward ((state1, state2), "nt, wr, t1, v1") post_zero;
  	      (* print_states_to_file post_zero; *)
  	      post_zero
  	  end
      end
  in

  (* let after_nwrite_t1_v1 = *)
  (*   if (check_status nwr_t1_v1 1) = Non_exist then non_exist *)
  (*   else begin *)
  (*     let st1 = fst(nwr_t1_v1) in *)
  (*     let st2 = snd(nwr_t1_v1) in *)
  (*     try *)
  (* 	Forward.find forward ((st1, st2), "nt, com, t1") *)
  (*     with Not_found -> *)
  (* 	let post_state = ncommit_t1 st1 st2 in *)
  (* 	match check_status post_state 1 with *)
  (* 	| Non_exist -> post_state *)
  (* 	| _ -> begin *)
  (* 	    print_to_files st1 st2 post_state "comt1"; *)
  (* 	    Forward.add forward ((st1, st2), "nt, com, t1") post_state; *)
  (* 	    post_state *)
  (*         end *)
  (*   end *)
  (* in *)

  let after_nwrite_t1_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t1, v2")
    with Not_found ->
      let post_state = nwrite_t1 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flg state2 with
       	  | 0 -> begin
  	      print_to_files state1 state2 post_state "nwrt1v2";
  	      Forward.add forward ((state1, state2), "nt, wr, t1, v2") post_state;
  	      (* print_states_to_file post_state; *)
  	      post_state
            end
  	  | _ -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t2")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "nwrt1v2";
  	      Forward.add forward ((state1, state2), "nt, wr, t1, v2") post_zero;
  	      (* print_states_to_file post_zero; *)
  	      post_zero
  	  end
      end
  in

  (* let after_nwrite_t1_v2 = *)
  (*   if (check_status nwr_t1_v2 1) = Non_exist then non_exist *)
  (*   else begin *)
  (*     let st1 = fst(nwr_t1_v2) in *)
  (*     let st2 = snd(nwr_t1_v2) in *)
  (*     try *)
  (* 	Forward.find forward ((st1, st2), "nt, com, t1") *)
  (*     with Not_found -> *)
  (* 	let post_state = ncommit_t1 st1 st2 in *)
  (* 	match check_status post_state 1 with *)
  (* 	| Non_exist -> post_state *)
  (* 	| _ -> begin *)
  (* 	    print_to_files st1 st2 post_state "comt1"; *)
  (* 	    Forward.add forward ((st1, st2), "nt, com, t1") post_state; *)
  (* 	    post_state *)
  (*         end *)
  (*   end *)
  (* in *)

  let after_nwrite_t2_v1 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v1")
    with Not_found ->
      let post_state = nwrite_t2 V1 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flg state1 with
       	  | 0 -> begin
  	      print_to_files state1 state2 post_state "nwrt2v1";
  	      Forward.add forward ((state1, state2), "nt, wr, t2, v1") post_state;
  	      (* print_states_to_file post_state; *)
  	      post_state
            end
  	  | _ -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "nwrt2v1";
  	      Forward.add forward ((state1, state2), "nt, wr, t2, v1") post_zero;
  	      (* print_states_to_file post_zero; *)
  	      post_zero
  	  end
      end
  in

  (* let after_nwrite_t2_v1 = *)
  (*   if (check_status nwr_t2_v1 1) = Non_exist then non_exist *)
  (*   else begin *)
  (*     let st1 = fst(nwr_t2_v1) in *)
  (*     let st2 = snd(nwr_t2_v1) in *)
  (*     try *)
  (* 	Forward.find forward ((st1, st2), "nt, com, t2") *)
  (*     with Not_found -> *)
  (* 	let post_state = ncommit_t2 st1 st2 in *)
  (* 	match check_status post_state 1 with *)
  (* 	| Non_exist -> post_state *)
  (* 	| _ -> begin *)
  (* 	    print_to_files st1 st2 post_state "comt2"; *)
  (* 	    Forward.add forward ((st1, st2), "nt, com, t2") post_state; *)
  (* 	    post_state *)
  (*         end *)
  (*   end *)
  (* in *)

  let after_nwrite_t2_v2 =
    try
      Forward.find forward ((state1, state2), "nt, wr, t2, v2")
    with Not_found ->
      let post_state = nwrite_t2 V2 state1 state2 in
      match check_status post_state 1 with
      |	Non_exist -> post_state
      |	_ -> begin
  	  match get_flg state1 with
       	  | 0 -> begin
  	      print_to_files state1 state2 post_state "nwrt2v2";
  	      Forward.add forward ((state1, state2), "nt, wr, t2, v2") post_state;
  	      (* print_states_to_file post_state; *)
  	      post_state
            end
  	  | _ -> begin
  	      let pre =
  		try
  		  Ser_trans.find ser_trans ((state1, state2), "ser, t1")
  		with Not_found -> non_exist
  	      in
  	      let post_zero = zero_flg (fst(post_state)) (snd(post_state)) in
  	      print_to_files (fst(pre)) (snd(pre)) post_zero "nwrt2v2";
  	      Forward.add forward ((state1, state2), "nt, wr, t2, v2") post_zero;
  	      (* print_states_to_file post_zero; *)
  	      post_zero
  	  end
      end
  in

  (* let after_nwrite_t2_v2 = *)
  (*   if (check_status nwr_t2_v2 1) = Non_exist then non_exist *)
  (*   else begin *)
  (*     let st1 = fst(nwr_t2_v2) in *)
  (*     let st2 = snd(nwr_t2_v2) in *)
  (*     try *)
  (* 	Forward.find forward ((st1, st2), "nt, com, t2") *)
  (*     with Not_found -> *)
  (* 	let post_state = ncommit_t2 st1 st2 in *)
  (* 	match check_status post_state 1 with *)
  (* 	| Non_exist -> post_state *)
  (* 	| _ -> begin *)
  (* 	    print_to_files st1 st2 post_state "comt2"; *)
  (* 	    Forward.add forward ((st1, st2), "nt, com, t2") post_state; *)
  (* 	    post_state *)
  (*         end *)
  (*   end *)
  (* in *)

  let state_list = [after_lc_rd_t1_v1; after_lc_rd_t1_v2; after_lc_rd_t2_v1; after_lc_rd_t2_v2; after_gl_rd_t1_v1; after_gl_rd_t1_v2;
		    after_gl_rd_t2_v1; after_gl_rd_t2_v2; after_wr_t1_v1; after_wr_t1_v2; after_wr_t2_v1; after_wr_t2_v2;
		    after_ser_t1; after_ser_t2; after_com_t1; after_com_t2; after_abt_t1; after_abt_t2; after_nread_t1_v1; after_nread_t1_v2;
		    after_nread_t2_v1; after_nread_t2_v2; after_nwrite_t1_v1; after_nwrite_t1_v2; after_nwrite_t2_v1; after_nwrite_t2_v2;
		   ] in
  let stateSet = StateSet.empty in
  let newStateSet = List.fold_left (fun acc st -> StateSet.add st acc) stateSet state_list in

  (*ref_loop := (!ref_loop) + 1;*)
  (*printf "original loop %d: \n" (!ref_loop);*)
  (*List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) state_list;*)

  let finalSet = StateSet.remove
      ((Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None), (Non_exist, 0, 0, (None, None), (None, None), (None, None), (None, None), None))
      newStateSet in
  let finalList = StateSet.elements finalSet in
  (* let newList = StateSet.elements finalSet in *)
  (*printf "all existing loop %d: \n" (!ref_loop);*)
  (*List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) newList;*)
  
  (*** Invalidated states do not need to be aborted right away. They can read or write before they are aborted, but they can never serialize so they never commit ***)

  (*** TODO: make the finalList as a function with acc argument and check the correctness of it ***)
(*   let finalList = List.fold_left (fun acc (st:statePair) -> *)
(*     begin *)
(*     let aborted = (Finished, 0, 0,(None, None), (None, None), (None, None), (None, None), None) in *)
(*     let proc_st = *)
(*       match (check_status st 1), (check_status st 2) with *)
(*       | Invalid, _ -> begin *)
(* 	  try *)
(* 	    Forward.find forward (st, "abt, t1") *)
(* 	  with Not_found -> *)
(* 	    let aborted_st = (aborted, snd(st)) in  *)
(* 	    match get_flg (snd st) with *)
(* 	    | 1 -> begin *)
(* 		let pre' = *)
(*   		  try *)
(*   		    Ser_trans.find ser_trans (((fst st), (snd st)), "ser, t2") *)
(*   		  with Not_found -> non_exist *)
(*   		in *)
(*   		let post_zero = zero_flg (fst(aborted_st)) (snd(aborted_st)) in *)
(*   		print_to_files (fst(pre')) (snd(pre')) post_zero "abtt1"; *)
(*   		Forward.add forward (st, "abt, t1") post_zero; *)
(* 		state_no := (!state_no) + 1; *)
(* 		post_zero *)
(* 	    end *)
(* 	    | _ -> begin  *)
(* 		print_to_files (fst(st)) (snd(st)) aborted_st "abtt1"; *)
(*        	    (\* no need to check if st has been printed before. If st hasn't appeared before it wouldn't have been aborted either, and vice versa. *\) *)
(* 		print_states_to_file st;  *)
(* 		state_no := (!state_no) + 1; (\* no need to print aborted_st or increase state_no by 2, because aborted_st = ((finished, ...), (...)), which must have appeared before *\) *)
(* 		Forward.add forward (st, "abt, t1") aborted_st; *)
(* 	    (\* let pre = *\) *)
(* 	    (\*   try *\) *)
(* 	    (\* 	Backward.find backward aborted_st *\) *)
(* 	    (\*   with Not_found -> *\) *)
(* 	    (\* 	Backward.add backward aborted_st {preStates = [st]}; *\) *)
(* 	    (\* 	{preStates = [st]} *\) *)
(* 	    (\* in *\) *)
(* 	    (\* pre.preStates <- (if List.mem (fst(st),snd(st)) pre.preStates then pre.preStates else ((fst(st),snd(st))::pre.preStates)); *\) *)
(* 	    (\* Backward.add backward aborted_st pre; *\) *)
(* 		aborted_st *)
(* 	    end *)
(* 	  end *)
(* (\*** TODO: differentiate tx and non-tx and print the non-final states of non-tx instructions ***\) *)
(*       | _, Invalid -> begin *)
(* 	  try *)
(* 	    Forward.find forward (st, "abt, t2") *)
(* 	  with Not_found -> *)
(*   	    let aborted_st = (fst(st), aborted) in  *)
(* 	    match get_flg (fst st) with *)
(* 	    | 1 -> begin *)
(* 		let pre' = *)
(*   		  try *)
(*   		    Ser_trans.find ser_trans (((fst st), (snd st)), "ser, t1") *)
(*   		  with Not_found -> non_exist *)
(*   		in *)
(*   		let post_zero = zero_flg (fst(aborted_st)) (snd(aborted_st)) in *)
(*   		print_to_files (fst(pre')) (snd(pre')) post_zero "abtt2"; *)
(*   		Forward.add forward (st, "abt, t2") post_zero; *)
(* 		state_no := (!state_no) + 1; *)
(* 		post_zero *)
(* 	    end *)
(* 	    | _ -> begin *)
(* 		print_to_files (fst(st)) (snd(st)) aborted_st "abtt2"; *)
(* 		print_states_to_file st; *)
(* 		state_no := (!state_no) + 1; *)
(* 		Forward.add forward (st, "abt, t2") aborted_st; *)
(* 	    (\* let pre = *\) *)
(* 	    (\*   try *\) *)
(* 	    (\* 	Backward.find backward aborted_st *\) *)
(* 	    (\*   with Not_found -> *\) *)
(* 	    (\* 	Backward.add backward aborted_st {preStates = [st]}; *\) *)
(* 	    (\* 	{preStates = [st]} *\) *)
(* 	    (\* in *\) *)
(* 	    (\* pre.preStates <- (if List.mem (fst(st),snd(st)) pre.preStates then pre.preStates else ((fst(st),snd(st))::pre.preStates)); *\) *)
(* 	    (\* Backward.add backward aborted_st pre; *\) *)
(* 		aborted_st *)
(* 	    end *)
(* 	  end *)
(*       | _, _ -> st *)
(*     in proc_st::acc end) [] newList *)
(*   in *)

  (*printf "polished loop %d: \n" (!ref_loop);*)
  (*List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) finalList;*)
  (*** TO TEST: print out the final list ***)
  finalList
end

let work_ref = ref (StateSet.add init_state_pair (StateSet.empty))
let visit_ref = ref (StateSet.empty)
let work_size = StateSet.cardinal (!work_ref);;
 
let rec reachable work_list visit_list filter_list = begin
  match work_list, visit_list, filter_list with
  | [], v, f -> f
  | hd::tl, v, f -> begin
      let new_v = hd::v in
      let new_f = begin
	match if_flg1 (fst(hd)) (snd(hd)) with
	| false -> hd::f
        | true -> f
      end in
      let post_w = get_post_state (fst(hd)) (snd(hd)) in
      let emptySet = StateSet.empty in
      let visitSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet new_v in
      let oldWorkSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet tl in
      let oldSet = StateSet.union visitSet oldWorkSet in
      let postSet = List.fold_left (fun acc st -> StateSet.add st acc) emptySet post_w in
      let newStates = StateSet.diff postSet oldSet in
      let newWorkList = StateSet.elements (StateSet.union oldWorkSet newStates) in
      reachable newWorkList new_v new_f
  end
end
;;

let visited = reachable [init_state_pair] [] [];;
let size = List.length visited;;
printf ("The number of the states is %d\n") ((!state_no) + size);;

let rec print_state_file stateList oc = begin
  match stateList with
  | [] -> close_out oc
  | hd::tl -> begin
      let hd_str = print_state_pair (fst(hd)) (snd(hd)) in
      let pol_hd = polish_state "" hd_str in
      fprintf oc "%s\n" pol_hd;
      state_no := (!state_no) + 1;
      print_state_file tl oc
  end
end;;

print_state_file visited o_f;;
print_state_file visited o_s;;

close_out o_t;;

let w_file = "Abort_consistency_non_tx_reference_automaton.ml"
let i_t = open_in t_file
let i_f = open_in f_file
let i_s = open_in s_file
let o_w = open_out w_file;;

fprintf o_w "Ops\ni:0\n";;

let t_list =[(* "lcrdt1v1"; "lcrdt1v2"; "lcrdt2v1"; "lcrdt2v2"; *) "rdt1v1"; "rdt1v2"; "rdt2v1"; "rdt2v2";
	     "wrt1v1"; "wrt1v2"; "wrt2v1"; "wrt2v2"; "nrdt1v1"; "nrdt1v2"; "nrdt2v1"; "nrdt2v2";
	     "nwrt1v1"; "nwrt1v2"; "nwrt2v1"; "nwrt2v2"; (* "sert1"; "sert2"; *) "comt1"; "comt2"; "abtt1"; "abtt2"
	    ]
let arg_list = List.fold_left (fun acc hd -> ((hd ^ ": 1")::acc)) [] t_list;;
List.iter (fun arg -> fprintf o_w "%s\n" arg) arg_list;;
fprintf o_w "\nAutomaton Reference\n\n";;

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


(* (\********** TESTING CODING **********\) *)
(* module StrSet = Set.Make(struct type t = string let compare = String.compare end) *)
(* let listSet = StrSet.empty *)
(* let fullSet1 = List.fold_left (fun acc st -> StrSet.add st acc) listSet ["a"; "b"; "c"; "d"; "e"] *)
(* let fullSet2 = List.fold_left (fun acc st -> StrSet.add st acc) listSet ["f"; "g"; "h"] *)
(* let listSize1 = StrSet.cardinal fullSet1 *)
(* let listSize2 = StrSet.cardinal fullSet2;; *)
(* (\*printf "The size of the string set1 is: %d\n"listSize1;;*\) *)
(* (\*printf "The size of the string set2 is: %d\n"listSize2;;*\) *)


(* let wrt2 = write_t2 V1 (fst(init_state_pair)) (snd(init_state_pair)) *)
(* let wrt2_str = print_state_pair (fst(wrt2)) (snd(wrt2)) *)

(* (\*let get_post = get_post_state (fst(init_state_pair)) (snd(init_state_pair))*\) *)
(* (\*let hashWrt2 = Forward.find forward (init_state_pair, "wr, t2, v1")*\) *)
(* (\*let postTest = print_state_pair (fst(hashWrt2)) (snd(hashWrt2));;*\) *)
(* (\*printf "Result in the hash table:\n %s\n" postTest;;*\) *)

(* let wrt1 = global_read_t1 V1 (fst(wrt2)) (snd(wrt2)) *)
(* let wrt1_str = print_state_pair (fst(wrt1)) (snd(wrt1));; *)
(* (\*printf "write v1 on t1:\n %s\n" wrt1_str;;*\) *)

(* let sert1 = serialize_t1 (fst(wrt1)) (snd(wrt1)) *)
(* let sert1_str = print_state_pair (fst(sert1)) (snd(sert1));; *)
(* (\*printf "serialize t1:\n %s\n" sert1_str;;*\) *)

(* let sert2 = serialize_t2 (fst(sert1)) (snd(sert1)) *)
(* let sert2_str = print_state_pair (fst(sert2)) (snd(sert2));; *)
(*    (\*printf "serialize t2:\n %s\n" sert2_str;;*\) *)

(* let comt2 = commit_t2 (fst(sert2)) (snd(sert2)) *)
(* let comt2_str = print_state_pair (fst(comt2)) (snd(comt2));; *)
(* (\*printf "commit t2:\n %s\n" comt2_str;;*\) *)

(* let comt1 = commit_t1 (fst(comt2)) (snd(comt2)) *)
(* let comt1_str = print_state_pair (fst(comt1)) (snd(comt1));; *)
(* (\*printf "commit t1:\n %s\n" comt1_str;;*\) *)

(* let testList = [((Invalid, 0, (None, None), (None, None), (None, None), (None, None), None), (Started, 0, (Some V1, None), (None, None), (None, None), (None, None), Some T1)); *)
(*  		(\* ((Serialized, (None, Some V2), (Some V1, None), (None, None), (None, None), None), (Invalid, (None, None), (None, None), (None, None), (None, None), None)); *\) *)
(* 		((Finished, 0, (None, None), (None, None), (None, None), (None, None), None), (Finished, 0, (None, None), (None, None), (None, None), (None, None), None)); *)
(* 		((Finished, 0, (None, None), (None, None), (None, None), (None, None), None), (Finished, 0, (None, None), (None, None), (None, None), (None, None), None)); *)
(* 	       ];; *)

(*   let final = List.fold_left (fun acc (st:statePair) ->  *)
(*     begin *)
(*     let aborted = (Finished, 0, (None, None), (None, None), (None, None), (None, None), None) in *)
(*     let proc_st =  *)
(*       match (check_status st 1), (check_status st 2) with  *)
(*       | Invalid, _ -> begin *)
(* 	  try *)
(* 	    Forward.find forward (st, "abt, t1") *)
(* 	  with Not_found -> *)
(* 	    let aborted_st = (aborted, snd(st)) in  *)
(* 	    Forward.add forward (st, "abt, t1") aborted_st;  *)
(* 	    aborted_st *)
(* 	  end *)
(*       | _, Invalid -> begin *)
(* 	  try *)
(* 	    Forward.find forward (st, "abt, t2") *)
(* 	  with Not_found -> *)
(*   	    let aborted_st = (fst(st), aborted) in  *)
(* 	    Forward.add forward (st, "abt, t2") aborted_st;  *)
(* 	    aborted_st *)
(* 	  end *)
(*       | _, _ -> st        *)
(*     in proc_st::acc end) [] testList *)
(*   ;; *)

(* (\*  printf "The testing final list is:\n";;*\) *)
(* (\*  List.iter (fun st -> printf "%s\n" (print_state_pair (fst(st)) (snd(st)))) final;;*\) *)

(* let rec run_word word_list state_pair = begin     *)
(*   match word_list with *)
(*   | [] -> state_pair *)
(*   | hd::tl ->  *)
(*       let post_state =  *)
(* 	match hd with *)
(* 	| "lc, rd, t1, v1" -> local_read_t1 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "lc, rd, t1, v2" -> local_read_t1 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "lc, rd, t2, v1" -> local_read_t2 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "lc, rd, t2, v2" -> local_read_t2 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "gl, rd, t1, v1" -> global_read_t1 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "gl, rd, t1, v2" -> global_read_t1 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "gl, rd, t2, v1" -> global_read_t2 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "gl, rd, t2, v2" -> global_read_t2 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "wr, t1, v1" -> write_t1 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "wr, t1, v2" -> write_t1 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "wr, t2, v1" -> write_t2 V1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "wr, t2, v2" -> write_t2 V2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "ser, t1" -> serialize_t1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "ser, t2" -> serialize_t2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "com, t1" -> commit_t1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "com, t2" -> commit_t2 (fst(state_pair)) (snd(state_pair)) *)
(* 	| "abt, t1" -> abort_t1 (fst(state_pair)) (snd(state_pair)) *)
(* 	| _ -> abort_t2 (fst(state_pair)) (snd(state_pair)) (\*i.e., "abt, t2"*\) *)
(*       in *)
(*       run_word tl post_state *)
(* end  *)

(* let if_ser = run_word ["gl, rd, t1, v2"; "gl, rd, t2, v2"; "ser, t1"; "ser, t2"; "wr, t2, v1"; "com, t2"; "wr, t1, v1"] init_state_pair *)
(* let if_ser_str = print_state_pair (fst(if_ser)) (snd(if_ser));; *)
(* (\*printf "The result of running a word is:\n %s\n" if_ser_str;;*\) *)


(* let start_state = ((Finished, 0, (None, None), (None, None), (None, None), (None, None), None), (Serialized, 0, (Some V1, Some V2), (Some V1, None), (None, None), (None, None), None)) *)
(* let test_post = run_word ["wr, t1, v1"; "wr, t1, v2"; "ser, t1"; "wr, t2, v2"; "com, t1"] start_state *)
(* let test_ser = print_state_pair (fst(test_post)) (snd(test_post));; *)
(* (\*printf  "The post state of the random state is:\n%s\n" test_ser;;*\) *)

(* let polished_test_ser = polish_state "" test_ser;; *)
(* (\*printf  "The polished post state of the random state is:\n%s\n" polished_test_ser;;*\) *)

(* let transition = "lc, rd, t1, v1" *)
(* let polished_transition = polish_transition "" transition;; *)
(* (\*printf  "The polished transition is:\n%s\n" polished_transition;;*\) *)

(* (\* let get_post_test = get_post_state (fst(init_state_pair)) (snd(init_state_pair)) *\) *)
(* (\* let (head: statePair) = List.hd get_post_test *\) *)
(* (\* let head_str = print_state_pair (fst(head)) (snd(head));; *\) *)
(* (\*printf "The head of the state list is:\n %s" head_str*\) *)

(* (\* failwith("stop here");; *\) *)

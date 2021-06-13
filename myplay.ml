open Array
open Color
open Command

let early = 48
let mid = 20
let latter = 17

type board = color array array

let count board color =
  let s = ref 0 in
    for i=1 to 8 do
      for j=1 to 8 do
        if board.(i).(j) = color then s := !s + 1
      done
    done;
    !s

let init_board () =
  let board = Array.make_matrix 10 10 none in
    for i=0 to 9 do
      board.(i).(0) <- sentinel ;
      board.(i).(9) <- sentinel ;
      board.(0).(i) <- sentinel ;
      board.(9).(i) <- sentinel ;
    done;
    board.(4).(4) <- white;
    board.(5).(5) <- white;
    board.(4).(5) <- black;
    board.(5).(4) <- black;
    board

let dirs = [ (-1,-1); (0,-1); (1,-1); (-1,0); (1,0); (-1,1); (0,1); (1,1) ]

let flippable_indices_line board color (di,dj) (i,j) =
  let ocolor = opposite_color color in
  let rec f (di,dj) (i,j) r =
    if board.(i).(j) = ocolor then
      g (di,dj) (i+di,j+dj) ( (i,j) :: r )
    else
      []
  and    g (di,dj) (i,j) r =
    if board.(i).(j) = ocolor then
      g (di,dj) (i+di,j+dj) ( (i,j) :: r )
    else if board.(i).(j) = color then
      r
    else
      [] in
    f (di,dj) (i,j) []

let flippable_indices board color (i,j) =
  let bs = List.map (fun (di,dj) -> flippable_indices_line board color (di,dj) (i+di,j+dj)) dirs in
    List.concat bs

let is_effective board color (i,j) =
  match flippable_indices board color (i,j) with
      [] -> false
    | _  -> true

let is_valid_move board color (i,j) =
  (board.(i).(j) = none) && is_effective board color (i,j)


let doMove board com color =
  match com with
      GiveUp  -> board
    | Pass    -> board
    | Mv (i,j) ->
	let ms = flippable_indices board color (i,j) in
	let _  = List.map (fun (ii,jj) -> board.(ii).(jj) <- color) ms in
	let _  = board.(i).(j) <- color in
    board

let rs = ref []

let doMove_safe board com color =
  match com with
      GiveUp  -> board
    | Pass    -> board
    | Mv (i,j) ->
  let ms = flippable_indices board color (i,j) in
  let _  = rs := ms; List.map (fun (ii,jj) -> board.(ii).(jj) <- color) ms in
  let _  = board.(i).(j) <- color in
    board

let resetMove board com color =
  match com with
      GiveUp  -> board
    | Pass    -> board
    | Mv (i,j) ->
  let op = opposite_color color in
  let _  = List.map (fun (ii,jj) -> board.(ii).(jj) <- op) !rs in
  let _  = board.(i).(j) <- none in
    board

let mix xs ys =
  List.concat (List.map (fun x -> List.map (fun y -> (x,y)) ys) xs)


let valid_moves board color =
  let ls = [1;2;3;4;5;6;7;8] in
  List.filter (is_valid_move board color)
    (mix ls ls)

(* ボードのコピー *)
let next_board board color (i,j) = doMove (Array.map (fun line -> Array.copy line) (Array.copy board)) (Mv (i,j)) color
  
let corner = [(1,1); (1,8); (8,1); (8,8)]
let semicorner = [((1,1), [(1,2); (2,2); (2,1)]); ((1,8), [(1,7); (2,7); (2,8)]); ((8,1), [(8,2); (7,2); (7,1)]); ((8,8), [(8,7); (7,7); (7,8)])]
let circ = [[(1,1); (1,2); (1,3); (1,4); (1,5); (1,6); (1,7); (1,8)];
            [(1,1); (2,1); (3,1); (4,1); (5,1); (6,1); (7,1); (8,1)];
            [(1,8); (2,8); (3,8); (4,8); (5,8); (6,8); (7,8); (8,8)];
            [(8,1); (8,2); (8,3); (8,4); (8,5); (8,6); (8,7); (8,8)]]
let md_line= [(2,3); (2,4); (2,5); (2,6); (3,2); (4,2); (5,2); (6,2); (3,7); (4,7); (5,7); (6,7); (7,3); (7,4); (7,5); (7,6)]


let corners board color =
  List.length (List.filter (fun (i,j) -> board.(i).(j) = color) corner)
let semicorners board color =
  List.fold_left (fun a n -> a + n) 0 
      (List.map (fun ((i,j),l) -> if board.(i).(j) = color then List.length (List.filter (fun (i,j) -> board.(i).(j) = opposite_color color) l)
                                  else if board.(i).(j) = none then List.length (List.filter (fun (i,j) -> board.(i).(j) = color) l)
                                  else 0) semicorner)

(* 確定石判定 *)
let rec rem_one ls n =
  match ls with
  | 1 :: l -> rem_one l (n+1)
  | _ -> if n < 0 || n = 4 then (ls,0) else (ls,n)

let wing board color circ =
  let ocolor = opposite_color color in
  let col = List.map (fun (i,j) -> if board.(i).(j) = color then 1 else if board.(i).(j) = ocolor then 0 else (-8)) circ in
  let (l1,n1) = rem_one col (-4) in
  let (l2,n2) = rem_one (List.rev l1) (-4) in
  let len = let a = List.fold_left (fun a n -> a + n) 0 l2 in if a > 0 then a else 0 in
  n1 + n2 + len
let fin_wing board color =
  List.fold_left (fun a n -> a + n) 0 (List.map (fun cir -> wing board color cir) circ)

let rec consecutive board color (i,j) (di,dj) r c d n =
  if n = 3 then (if board.(i).(j) = color then 
   1 + consecutive board color (i+di,j+dj) (di,dj) r c d (n-1) else 0)
  else if n = 2 then
    if board.(i-di).(j) = color then
      if board.(i).(j-dj) = color then
        if board.(i).(j) = color then 
         3 + consecutive board color (i+di,j+dj) (di,dj) r c d (n-1)
        else 2 + consecutive board color (i+di,j+dj) (di,dj) r c 0 (n-1)
      else 1 + consecutive board color (i+di,j+dj) (di,dj) r 0 0 (n-1)
    else
      if board.(i).(j-dj) = color then
        1 + consecutive board color (i+di,j+dj) (di,dj) 0 c 0 (n-1)
      else 0
  else if n = 1 then
    if c = 0 then
      if board.(i-2*di).(j) = color then 
       1 + consecutive board color (i+di,j+dj) (di,dj) r 0 0 (n-1) else 0
    else if r = 0 then
      if board.(i).(j-2*dj) = color then 
       1 + consecutive board color (i+di,j+dj) (di,dj) 0 c 0 (n-1) else 0
    else
      if d = 0 then
        if board.(i-2*di).(j) = color then
          if board.(i).(j-2*dj) = color then
            2 + consecutive board color (i+di,j+dj) (di,dj) r c 0 (n-1)
          else 1 + consecutive board color (i+di,j+dj) (di,dj) r 0 0 (n-1)
        else 0
      else
        if board.(i-2*di).(j) = color then
          if board.(i).(j-2*dj) = color then
            if board.(i-di).(j) = color then
              if board.(i).(j-dj) = color then
                if board.(i).(j) = color then
                  5 + consecutive board color (i+di,j+dj) (di,dj) r c d (n-1)
                else 4 + consecutive board color (i+di,j+dj) (di,dj) r c 2 (n-1)
              else 3 + consecutive board color (i+di,j+dj) (di,dj) r c 3 (n-1)
            else
              if board.(i).(j-dj) = color then
                3 + consecutive board color (i+di,j+dj) (di,dj) r c 4 (n-1)
              else 2 + consecutive board color (i+di,j+dj) (di,dj) r c 0 (n-1)
          else 
            if board.(i-di).(j) = color then
              2 + consecutive board color (i+di,j+dj) (di,dj) r 0 4 (n-1)
            else 1 + consecutive board color (i+di,j+dj) (di,dj) r 0 0 (n-1)
        else
          if board.(i).(j-2*dj) = color then
            if board.(i).(j-dj) = color then
              2 + consecutive board color (i+di,j+dj) (di,dj) 0 c 3 (n-1)
            else
              1 + consecutive board color (i+di,j+dj) (di,dj) 0 c 0 (n-1)
          else 0
  else
    if c = 0 then
      if d = 3 then
        if board.(i-3*di).(j) = color then
          if board.(i-2*di).(j) = color then 
          2 else 1
        else 0
      else (if board.(i-3*di).(j) = color then 
       1 else 0)
    else if r = 0 then
      if d = 4 then
        if board.(i).(j-3*dj) = color then
          if board.(i).(j-2*dj) = color then 
          2 else 1
        else 0
      else (if board.(i).(j-3*dj) = color then 
      1 else 0)
    else
      if d = 5 then
        if board.(i-3*di).(j) = color && board.(i).(j-3*dj) = color then
          if board.(i-2*di).(j) = color then
            if board.(i-di).(j) = color then
              if board.(i).(j-2*dj) = color then
                if board.(i).(j-dj) = color then
                  if board.(i).(j) = color then 
                    7 else 6
                else 5
              else 4
            else 
              if board.(i).(j-2*dj) = color then
                if board.(i).(j-dj) = color then
                  5 else 4
              else 3
          else
            if board.(i).(j-2*dj) = color then
              if board.(i).(j-dj) = color then 
                4 else 3
            else 2
        else if board.(i-3*di).(j) = color then
          if board.(i-2*di).(j) = color then
            if board.(i-di).(j) = color then
              3 else 2
          else 1
        else if board.(i).(j-3*dj) = color then
          if board.(i).(j-2*dj) = color then
            if board.(i).(j-dj) = color then 
             3 else 2
          else 1
        else 0
      else if d = 4 then
        if board.(i-3*di).(j) = color then
          if board.(i).(j-3*dj) = color then
            if board.(i).(j-2*dj) = color then 
            3 else 2
          else 1
        else
          if board.(i).(j-3*dj) = color then
            if board.(i).(j-2*dj) = color then
             2 else 1
          else 0
      else
        if board.(i).(j-3*dj) = color then
          if board.(i-3*di).(j) = color then
            if board.(i-2*di).(j) = color then
             3 else 2
          else 1
        else
          if board.(i-3*di).(j) = color then
            if board.(i-2*di).(j) = color then 
            2 else 1
          else 0

let final_stone board color =
  List.fold_left (fun a n -> a + n) 0 (List.map2 (fun (i,j) (di,dj) -> consecutive board color (i,j) (di,dj) 1 1 1 3) corner [(1,1); (1,-1); (-1,1); (-1,-1)]) + fin_wing board color

(* 開放度判定 *)
let openness board (i,j) =
  let bs = List.map (fun (di,dj) -> if board.(i+di).(j+dj) = none then 1 else 0) dirs in
    List.fold_left (fun a n -> a + n) 0 bs

let rec my_openness board flippable_list min =
  match flippable_list with
  | [] -> min
  | (i,j) :: fl -> let n = openness board (i,j) in
                   if n < min then my_openness board fl n
                   else my_openness board fl min

let rec opp_min_openness board color os min =
  match os with
  | [] -> min
  | (i,j) :: xs -> let fl = flippable_indices board color (i,j) in
                    let openness = my_openness board fl 9 in
                    if openness < min then opp_min_openness board color xs openness
                    else opp_min_openness board color xs min

(* early stage用 *)
let rec early_scoring board color (i,j) =
  let fl = flippable_indices board color (i,j) in
  let _ = doMove_safe board (Mv (i,j)) color in
  let ocolor = opposite_color color in
  let len = List.length fl in
  let my_open = my_openness board fl 9 in
  let opp_open = opp_min_openness board ocolor (valid_moves board ocolor) 9 in
  let corner_point = 5 * (corners board color - corners board ocolor) in
  let semicorner_point = (-3) * (semicorners board color) in
  let _ = resetMove board (Mv (i,j)) color in
  (5 - len) + (10 - my_open) + opp_open + corner_point + semicorner_point

(* 壁の個数判定 *)
let rec get_start_point board color ocolor (i,j) =
  if board.(i+1).(j+1) = color || board.(i+1).(j+1) = ocolor then (i,j)
  else 
    if board.(i).(j+1) = color || board.(i).(j+1) = ocolor then (i,j)
    else get_start_point board color ocolor (i+1,j+1)

let rec count_my_wall board color ocolor (s,e) (i,j) (k,l) f =
  if k = s && l = e then (if s = 0 then 0 else 1)
  else
    match k,l with
    | 0,9 | 9,0 | 9,9 -> count_my_wall board color ocolor (s,e) (k,l) (k+l-j,l-k+i) 0
    | 0,_ | 9,_ | _,0 | _,9 -> 
        if board.(k+l-j).(l-k+i) = color || board.(k+l-j).(l-k+i) = ocolor then
          (* 来た方向から見て左側が空いていないとき反対側に進む *)
          count_my_wall board color ocolor (s,e) (k,l) (2*k-i,2*l-j) 0
        else
          (* 来た方向から見て左側が空いているとき左側に進む *)
          count_my_wall board color ocolor (s,e) (k,l) (k+l-j,l-k+i) 1
    | _,_ -> if board.(2*k-i).(2*l-j) = color || board.(2*k-i).(2*l-j) = ocolor then
                if board.(k+l-j).(l-k+i) = color || board.(k+l-j).(l-k+i) = ocolor then
                  if board.(k-l+j).(l+k-i) = color || board.(k-l+j).(l+k-i) = ocolor then
                    (* 来た方向以外空いていないとき来たところに戻る、前右確認 *)
                    if board.(2*k-i).(2*l-j) = color && board.(k-l+j).(l+k-i) = color && f = 0 then  
                      2 + count_my_wall board color ocolor (s,e) (k,l) (i,j) 0
                    else if board.(2*k-i).(2*l-j) = color || board.(k-l+j).(l+k-i) = color && f = 0 then
                      1 + count_my_wall board color ocolor (s,e) (k,l) (i,j) 0
                    else count_my_wall board color ocolor (s,e) (k,l) (i,j) 0
                  else
                    (* 来た方向から見て右側だけ空いているとき右側に進む、一個前確認 *)
                    if board.(k+l-j).(l-k+i) = color && f = 0 then
                      1 + count_my_wall board color ocolor (s,e) (k,l) (k-l+j,l+k-i) 0
                    else if board.(2*k-i).(2*l-j) = color && f = 1 then
                      1 + count_my_wall board color ocolor (s,e) (k,l) (k-l+j,l+k-i) 0
                    else
                      count_my_wall board color ocolor (s,e) (k,l) (k-l+j,l+k-i) 0
                else
                  (* 来た方向から見て左側が空いているとき左側に進む *)
                  count_my_wall board color ocolor (s,e) (k,l) (k+l-j,l-k+i) 0
            else
                if board.(k+l-j).(l-k+i) = color || board.(k+l-j).(l-k+i) = ocolor then
                  (* 来た方向と反対側が空いていて左側が空いていないとき反対側に進む、一個前確認 *)
                  if board.(k+l-j).(l-k+i) = color && f = 0 then
                      1 + count_my_wall board color ocolor (s,e) (k,l) (2*k-i,2*l-j) 0   
                  else
                    count_my_wall board color ocolor (s,e) (k,l) (2*k-i,2*l-j) 0   
                else
                  (* 来た方向から見て反対側と左側が空いているとき左側に進む *)
                  count_my_wall board color ocolor (s,e) (k,l) (k+l-j,l-k+i) 1

let my_wall_and_final board color =
  let ocolor = opposite_color color in
  let (i,j) = get_start_point board color ocolor (0,0) in
  let (k,l) = if board.(i).(j+1) = color || board.(i).(j+1) = ocolor then (i-1,j)
              else (i,j+1) in
  let num = count_my_wall board color ocolor (i,j) (i,j) (k,l) 0 in
  let mfin = final_stone board color in
  let ofin = final_stone board ocolor in
  15 - 2 * num + 3 * mfin + (10 - 3 * ofin)

(* 石と枠に囲まれているか判定 *)
let stuffer board (i,j) =
  let bs = List.map (fun (di,dj) -> if board.(i+di).(j+dj) = none then 1 else 0) dirs in
  if List.fold_left (fun a n -> a + n) 0 bs = 0 then 5 else 0 

(* mid stage用 *)
let rec mid_scoring board color (i,j) =
  let _ = doMove_safe board (Mv (i,j)) color in
  let ocolor = opposite_color color in
  let mid = List.length (List.filter (fun (i,j) -> board.(i).(j) = color) md_line) in
  let wf = my_wall_and_final board color in
  let corner_point = 10 * (corners board color - corners board ocolor) in
  let semicorner_point = (-3) * (semicorners board color) in
  let opp_corner = if List.filter (fun (i,j) -> List.mem (i,j) corner) (valid_moves board ocolor) = [] then 0 else (-20) in
  let _ = resetMove board (Mv (i,j)) color in
  (5 - mid) + wf + corner_point + semicorner_point + (stuffer board (i,j)) + opp_corner

(* latter stage 用 *)
let rec latter_scoring board color (i,j) =
  let _ = doMove_safe board (Mv (i,j)) color in
  let ocolor = opposite_color color in
  let corner_point = 10 * (corners board color - corners board ocolor) in
  let semicorner_point = (-3) * (semicorners board color) in
  let opp_corner = if List.filter (fun (i,j) -> List.mem (i,j) corner) (valid_moves board ocolor) = [] then 0 else (-15) in
  let mfin = final_stone board color in
  let ofin = final_stone board ocolor in
  let _ = resetMove board (Mv (i,j)) color in
  corner_point + semicorner_point + (stuffer board (i,j)) + opp_corner + (mfin - ofin) * 2

(* 先読み *)
let scoring board color (i,j) =
  let remain = 64 - (count board black + count board white) in
  if remain > early then
    early_scoring board color (i,j)
  else if remain > mid then
    mid_scoring board color (i,j)
  else
    latter_scoring board color (i,j)

let sort_node board color ms =
  let comb = List.combine (List.map (fun (i,j) -> scoring board color (i,j)) ms) ms in
  let (_,sorted) = List.split (List.fast_sort (fun (i1,_) (i2,_) -> Pervasives.compare i2 i1) comb) in
  sorted

let rec alpha_beta_max board turn my_color n ms max m =
  match ms with
  | [] -> m
  | (i,j) :: xs -> let tmp = if n = 0 then scoring board turn (i,j)
                             else read_ahead (next_board board turn (i,j)) turn my_color (n-1) m in
                   if tmp <= max then 
                      if tmp > m then alpha_beta_max board turn my_color n xs max tmp
                      else alpha_beta_max board turn my_color n xs max m
                   else tmp
and alpha_beta_min board turn my_color n ms min m =
  match ms with
  | [] -> m
  | (i,j) :: xs -> let tmp = read_ahead (next_board board turn (i,j)) turn my_color (n-1) m in
                   if tmp >= min then
                      if tmp < m then alpha_beta_min board turn my_color n xs min tmp
                      else alpha_beta_min board turn my_color n xs min m
                   else tmp
and read_ahead board color my_color n ab =
  let turn = opposite_color color in
  let ms = valid_moves board turn in
  if n = 0 then
    if ms = [] then (if count board turn = 0 then (-99) else if count board color = 0 then 99 else -60)
    else alpha_beta_max board turn my_color n (sort_node board turn ms) ab (-1000)
  else
    if ms = [] then read_ahead board turn my_color (n-1) ab
    else if turn = my_color then
      alpha_beta_max board turn my_color n (sort_node board turn ms) ab (-1000)
    else
      alpha_beta_min board turn my_color n (sort_node board turn ms) ab 1000

(* 読み切り用 *)
let late_scoring board color (i,j) =
  let _ = doMove_safe board (Mv (i,j)) color in
  let ocolor = opposite_color color in
  let corner_point = 3 * (corners board color - corners board ocolor) in
  let semicorner_point = (-2) * (semicorners board color) in
  let my =  List.length (valid_moves board color) in
  let opp =  List.length (valid_moves board ocolor) in
  let _ = resetMove board (Mv (i,j)) color in
  (stuffer board (i,j)) + my +  (10 - opp) + corner_point + semicorner_point

let rec alpha_beta_late_max board turn my_color flag ms max m =
  if max = -1 then -1
  else if flag then let tmp = if count board my_color > count board (opposite_color my_color) then 1 else -1 in
    if tmp > m then tmp else m
  else
    match ms with
    | [] -> m
    | (i,j) :: xs -> let tmp = read_ahead_late (next_board board turn (i,j)) turn my_color m in
  if tmp > m then alpha_beta_late_max board turn my_color flag xs max tmp
                     else alpha_beta_late_max board turn my_color flag xs max m
and alpha_beta_late_min board turn my_color ms min m =
  if min = 1 then 1
  else 
    match ms with
    | [] -> m
    | (i,j) :: xs -> let tmp = read_ahead_late (next_board board turn (i,j)) turn my_color m in
                     if tmp < m then alpha_beta_late_min board turn my_color xs min tmp
                     else alpha_beta_late_min board turn my_color xs min m
and read_ahead_late board color my_color ab =
  let turn = opposite_color color in
  let ms = valid_moves board turn in
  if ms = [] then 
    if valid_moves board color = [] && turn = my_color then alpha_beta_late_max board turn my_color true ms ab (-2)
    else read_ahead_late board turn my_color ab
  else if turn = my_color then alpha_beta_late_max board turn my_color false ms ab (-2)
  else alpha_beta_late_min board turn my_color ms ab 2

(* 得点計算 *)
let rec alpha_beta board color ms m (k,l) loop =
  match ms with
  | [] -> (k,l)
  | (i,j) :: xs -> let tmp = read_ahead (next_board board color (i,j)) color color loop m in
                   if tmp > m then alpha_beta board color xs tmp (i,j) loop
                   else if tmp = m then
                      if Random.bool () then alpha_beta board color xs tmp (i,j) loop
                      else alpha_beta board color xs m (k,l) loop
                   else alpha_beta board color xs m (k,l) loop

let rec alpha_beta_late board color ms =
  match ms with
  | [] -> raise Not_found
  | (i,j) :: xs -> let tmp = read_ahead_late (next_board board color (i,j)) color color (-2) in
                    if tmp = 1 then (i,j)
                    else alpha_beta_late board color xs

let play board color mytime =
  let ms = valid_moves board color in
  let remain = 64 - (count board black + count board white) in
    if ms = [] then
      Pass
    else
      if remain > early then
        let (i,j) = alpha_beta board color (sort_node board color ms) (-1000) (List.hd ms) 3 in
        Mv (i,j)
      else if remain > latter then
        let len = List.length ms in
        let loop =  if len > 8 || mytime < 25000 then 3 else 5 in
        let (i,j) = alpha_beta board color (sort_node board color ms) (-1000) (List.hd ms) loop in
        Mv (i,j)
      else 
        let m = sort_node board color ms in
        let len = List.length ms in        
        let (i,j) = if ((len > 9 || mytime < 10000) && remain > 13) || ((len > 8 || mytime < 20000) && remain > 15) then alpha_beta board color m (-1000) (List.hd m) 3
                    else try alpha_beta_late board color m with Not_found -> alpha_beta board color m (-1000) (List.hd m) 3 in
        Mv (i,j)

let print_board board =
  print_endline " |A B C D E F G H ";
  print_endline "-+----------------";
  for j=1 to 8 do
    print_int j; print_string "|";
    for i=1 to 8 do
      print_color (board.(i).(j)); print_string " "
    done;
    print_endline ""
  done;
  print_endline "  (X: Black,  O: White)"    

let report_result board =
  let _ = print_endline "========== Final Result ==========" in
  let bc = count board black in
  let wc = count board white in
    if bc > wc then
      print_endline "*Black wins!*"
    else if bc < wc then
      print_endline "*White wins!*"
    else
      print_endline "*Even*";
    print_string "Black: "; print_endline (string_of_int bc);
    print_string "White: "; print_endline (string_of_int wc);
    print_board board

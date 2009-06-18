(*
 *  monitor.ml
 *
 *  Made by (Kirchner DIMITRI)
 *  Login   <dimitri@logic-3.CS.McGill.CA>
 *
 *  Started on  Wed May  6 11:13:24 2009 Kirchner DIMITRI
 *  Last update Wed May  6 11:13:24 2009 Kirchner DIMITRI
 *
 *)

(*
 * on: is true if we call the interpreter with argument: +t
 * onf: is true if we call the interpreter with argument: +tfile
 *)
let on = ref false;;
let onf = ref false;;

(*
 * We create two arrays which will contain the differents steps of the type checking
 * and the binding result.
 *)
let valeurs = Array.make 17 0. ;;
let etapes = Array.make 17 "" ;;


(* @brief Initialise the array named "etapes". *)
let init_tab () = 
  etapes.(0) <- "Constant Elaboration";
  etapes.(1) <- "Constant Reconstruction";
  etapes.(2) <- "Constant Abstraction";
  etapes.(3) <- "Constant Check";
  
  etapes.(4) <- "Type Elaboration";
  etapes.(5) <- "Type Reconstruction";
  etapes.(6) <- "Type Abstraction";
  etapes.(7) <- "Type Check";
  
  etapes.(8) <- "Function Elaboration";
  etapes.(9) <- "Function Reconstruction";
  etapes.(10) <- "Function Abstraction";
  etapes.(11) <- "Function Check";
  
  etapes.(12) <- "Function Type Elaboration";
  etapes.(13) <- "Function Type Reconstruction";
  etapes.(14) <- "Function Type Abstraction";
  etapes.(15) <- "Function Type Check";

  etapes.(16) <- "Normalisation";;

init_tab ();;


(* @brief Add the time to the bound flag. *)
let writeTime (name, time) =
  match name with
      n when n = etapes.(0) -> valeurs.(0) <- valeurs.(0) +. time;
    | n when n = etapes.(1) -> valeurs.(1) <- valeurs.(1) +. time;
    | n when n = etapes.(2) -> valeurs.(2) <- valeurs.(2) +. time;
    | n when n = etapes.(3) -> valeurs.(3) <- valeurs.(3) +. time;
    | n when n = etapes.(4) -> valeurs.(4) <- valeurs.(4) +. time;
    | n when n = etapes.(5) -> valeurs.(5) <- valeurs.(5) +. time;
    | n when n = etapes.(6) -> valeurs.(6) <- valeurs.(6) +. time;
    | n when n = etapes.(7) -> valeurs.(7) <- valeurs.(7) +. time;
    | n when n = etapes.(8) -> valeurs.(8) <- valeurs.(8) +. time;
    | n when n = etapes.(9) -> valeurs.(9) <- valeurs.(9) +. time;
    | n when n = etapes.(10) -> valeurs.(10) <- valeurs.(10) +. time;
    | n when n = etapes.(11) -> valeurs.(11) <- valeurs.(11) +. time;
    | n when n = etapes.(12) -> valeurs.(12) <- valeurs.(12) +. time;
    | n when n = etapes.(13) -> valeurs.(13) <- valeurs.(13) +. time;
    | n when n = etapes.(14) -> valeurs.(14) <- valeurs.(14) +. time;
    | n when n = etapes.(15) -> valeurs.(15) <- valeurs.(15) +. time;
    | n when n = etapes.(16) -> valeurs.(16) <- valeurs.(16) +. time;
    | _ -> Printf.printf "Non existing argument for function writeTime (name, time).\n";;


(* 
 * @brief If the flag "+t" or "+tfile" is on, take the time before and after the 
 * function f and call writeTime ().
 *)
let timer (name, f) = 
  if (!on || !onf) then
    (*  Printf.printf "In timer\n"; *)
    let timeBef = Unix.gettimeofday() in 
     let result  = f() in
    let timeAft = Unix.gettimeofday() in 
    (* let timeAft = Unix.times () in  *)
      writeTime (name, timeAft -. timeBef);
      result;
  else 
    f();;


(*
 * @brief Print the timing array.
 * If the flag "on" is true, print it in the shell, after the execution.
 * If the flag "onf" is true, print it in the file named "time.txt".
 *)
let print_timer () = 
  if !on then
    let _ = Printf.printf "\n  ## Timer Information: ##\n\n" in
      for i=0 to 3 do
	for j=0 to 3 do
	  Printf.printf "%s: " etapes.(4*i+j);
	  Printf.printf "%f\n" valeurs.(4*i+j)
	done;
	Printf.printf "\n"
      done;
      Printf.printf "\nTOTAL:\n Elaboration: %f" (valeurs.(0)+.valeurs.(4)+.valeurs.(8)+.valeurs.(12));
      Printf.printf "\n Reconstruction: %f" (valeurs.(1)+.valeurs.(5)+.valeurs.(9)+.valeurs.(13));
      Printf.printf "\n Abstraction: %f" (valeurs.(2)+.valeurs.(6)+.valeurs.(10)+.valeurs.(14));
      Printf.printf "\n Check: %f\n" (valeurs.(3)+.valeurs.(7)+.valeurs.(11)+.valeurs.(15));
      Printf.printf "\n Normalisation: %f\n" valeurs.(16);
      
      
      if !onf then
	let channel = open_out "time.txt" in
	let _ = Printf.fprintf channel "\n  ## Timer Information: ##\n\n" in
	  for i=0 to 3 do
	    for j=0 to 3 do
	      Printf.fprintf channel "%s: " etapes.(4*i+j);
	      Printf.fprintf channel "%f\n" valeurs.(4*i+j)
	    done;
	    Printf.fprintf channel "\n"
	  done;
	  Printf.fprintf channel "\nTOTAL:\n Elaboration: %f" (valeurs.(0)+.valeurs.(4)+.valeurs.(8)+.valeurs.(12));
	  Printf.fprintf channel "\n Reconstruction: %f" (valeurs.(1)+.valeurs.(5)+.valeurs.(9)+.valeurs.(13));
	  Printf.fprintf channel "\n Abstraction: %f" (valeurs.(2)+.valeurs.(6)+.valeurs.(10)+.valeurs.(14));
	  Printf.fprintf channel "\n Check: %f\n" (valeurs.(3)+.valeurs.(7)+.valeurs.(11)+.valeurs.(15));
	  Printf.fprintf channel "\n Normalisation: %f\n" valeurs.(16);

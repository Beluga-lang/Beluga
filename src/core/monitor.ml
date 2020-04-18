open Support

(*
 *  monitor.ml
 *
 *  Made by Dimitri Kirchner
 *  Login   <dimitri@logic-3.CS.McGill.CA>
 *
 *  Started on  Wed May  6 11:13:24 2009 Dimitri Kirchner
 *  Last update Mon Jun 15 11:13:24 2009 Dimitri Kirchner
 *)

let on = ref false;;
let onf = ref false;;

(* TODO this module should be rewritten to use hashtable or something
   and furthermore to use English variable names.
   -je
 *)

(*
 * We create four arrays which will contain the differents steps of the type checking
 * and the binding result.
 *)
let etapes = Array.make 17 "" ;;
let valeurs_realtime = Array.make 17 0. ;;
let valeurs_utime = Array.make 17 0. ;;
let valeurs_stime = Array.make 17 0. ;;


(* @brief Initialise the array named "etapes" to the different steps. *)
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


(* @brief Add the time to the bound flag in the array named "array". *)
let writeTime (name, time, array) =
  let found = ref false in
  for i = 1 to 16 do
    if Misc.String.equals name etapes.(i)
    then
      begin
        array.(i) <- array.(i) +. time;
        found := true
      end
  done;
  if not !found
  then
    Printf.printf "Non existing argument for function writeTime (name, time).\n"

(* Get the time before and after executing function f. Then call writeTime() to save data. *)
let timer (name, f) =
  if !on || !onf
  then
    begin
      let timeRealBef = Unix.gettimeofday () in
      let timeBef = Unix.times () in
      let result = f () in
      let timeAft = Unix.times () in
      let timeRealAft = Unix.gettimeofday () in
      writeTime (name, timeAft.Unix.tms_utime -. timeBef.Unix.tms_utime, valeurs_utime);
      writeTime (name, timeAft.Unix.tms_stime -. timeBef.Unix.tms_stime, valeurs_stime);
      writeTime (name, timeRealAft -. timeRealBef, valeurs_realtime);
      result;
    end
  else
    f ();;


(*Help for print_timer*)
let addR i =
  (valeurs_realtime.(i) +. valeurs_realtime.(i + 4) +. valeurs_realtime.(i + 8) +. valeurs_realtime.(i + 12));;
let addU i =
  (valeurs_utime.(i) +. valeurs_utime.(i + 4) +. valeurs_utime.(i + 8) +. valeurs_utime.(i + 12));;
let addS i =
  (valeurs_stime.(i) +. valeurs_stime.(i + 4) +. valeurs_stime.(i + 8) +. valeurs_stime.(i + 12));;


(*
 * @brief Print the timing arrays.
 * If the flag "on" is true, print it in the shell, after the execution.
 * If the flag "onf" is true, print it in the file named "time.txt".
 *)
let print_timer () =
  if !on
  then
    begin
      Printf.printf "\n                ## Timer Information: ##\n\n";
      Printf.printf "    Steps:                   | Real time: | User time: | System time: \n";

      Printf.printf "%s         |  %.6f  |  %.6f  |  %.6f\n" etapes.(0) valeurs_realtime.(0) valeurs_utime.(0) valeurs_stime.(0);
      Printf.printf "%s      |  %.6f  |  %.6f  |  %.6f\n" etapes.(1) valeurs_realtime.(1) valeurs_utime.(1) valeurs_stime.(1);
      Printf.printf "%s         |  %.6f  |  %.6f  |  %.6f\n" etapes.(2) valeurs_realtime.(2) valeurs_utime.(2) valeurs_stime.(2);
      Printf.printf "%s               |  %.6f  |  %.6f  |  %.6f\n" etapes.(3) valeurs_realtime.(3) valeurs_utime.(3) valeurs_stime.(3);

      Printf.printf "%s             |  %.6f  |  %.6f  |  %.6f\n" etapes.(4) valeurs_realtime.(4) valeurs_utime.(4) valeurs_stime.(4);
      Printf.printf "%s          |  %.6f  |  %.6f  |  %.6f\n" etapes.(5) valeurs_realtime.(5) valeurs_utime.(5) valeurs_stime.(5);
      Printf.printf "%s             |  %.6f  |  %.6f  |  %.6f\n" etapes.(6) valeurs_realtime.(6) valeurs_utime.(6) valeurs_stime.(6);
      Printf.printf "%s                   |  %.6f  |  %.6f  |  %.6f\n" etapes.(7) valeurs_realtime.(7) valeurs_utime.(7) valeurs_stime.(7);

      Printf.printf "%s         |  %.6f  |  %.6f  |  %.6f\n" etapes.(8) valeurs_realtime.(8) valeurs_utime.(8) valeurs_stime.(8);
      Printf.printf "%s      |  %.6f  |  %.6f  |  %.6f\n" etapes.(9) valeurs_realtime.(9) valeurs_utime.(9) valeurs_stime.(9);
      Printf.printf "%s         |  %.6f  |  %.6f  |  %.6f\n" etapes.(10) valeurs_realtime.(10) valeurs_utime.(10) valeurs_stime.(10);
      Printf.printf "%s               |  %.6f  |  %.6f  |  %.6f\n" etapes.(11) valeurs_realtime.(11) valeurs_utime.(11) valeurs_stime.(11);

      Printf.printf "%s    |  %.6f  |  %.6f  |  %.6f\n" etapes.(12) valeurs_realtime.(12) valeurs_utime.(12) valeurs_stime.(12);
      Printf.printf "%s |  %.6f  |  %.6f  |  %.6f\n" etapes.(13) valeurs_realtime.(13) valeurs_utime.(13) valeurs_stime.(13);
      Printf.printf "%s    |  %.6f  |  %.6f  |  %.6f\n" etapes.(14) valeurs_realtime.(14) valeurs_utime.(14) valeurs_stime.(14);
      Printf.printf "%s          |  %.6f  |  %.6f  |  %.6f\n" etapes.(15) valeurs_realtime.(15) valeurs_utime.(15) valeurs_stime.(15);

      Printf.printf "\nTOTAL:";
      Printf.printf "\n Elaboration:                |  %.6f  |  %.6f  |  %.6f" (addR 0) (addU 0) (addS 0);
      Printf.printf "\n Reconstruction:             |  %.6f  |  %.6f  |  %.6f" (addR 1) (addU 1) (addS 1);
      Printf.printf "\n Abstraction:                |  %.6f  |  %.6f  |  %.6f" (addR 2) (addU 2) (addS 2);
      Printf.printf "\n Check:                      |  %.6f  |  %.6f  |  %.6f\n" (addR 3) (addU 3) (addS 3);
      Printf.printf "\n Normalisation:              |  %.6f  |  %.6f  |  %.6f\n" valeurs_realtime.(16) valeurs_utime.(16) valeurs_stime.(16);
    end
  else if !onf
  then
    begin
      let channel = open_out "time.txt" in
      Printf.fprintf channel "\n               ## Timer Information: ##\n\n";
      Printf.fprintf channel "    Steps:                   | Real time: | User time: | System time: \n";

      Printf.fprintf channel "%s         |  %.6f  |  %.6f  |  %.6f\n" etapes.(0) valeurs_realtime.(0) valeurs_utime.(0) valeurs_stime.(0);
      Printf.fprintf channel "%s      |  %.6f  |  %.6f  |  %.6f\n" etapes.(1) valeurs_realtime.(1) valeurs_utime.(1) valeurs_stime.(1);
      Printf.fprintf channel "%s         |  %.6f  |  %.6f  |  %.6f\n" etapes.(2) valeurs_realtime.(2) valeurs_utime.(2) valeurs_stime.(2);
      Printf.fprintf channel "%s               |  %.6f  |  %.6f  |  %.6f\n" etapes.(3) valeurs_realtime.(3) valeurs_utime.(3) valeurs_stime.(3);

      Printf.fprintf channel "%s             |  %.6f  |  %.6f  |  %.6f\n" etapes.(4) valeurs_realtime.(4) valeurs_utime.(4) valeurs_stime.(4);
      Printf.fprintf channel "%s          |  %.6f  |  %.6f  |  %.6f\n" etapes.(5) valeurs_realtime.(5) valeurs_utime.(5) valeurs_stime.(5);
      Printf.fprintf channel "%s             |  %.6f  |  %.6f  |  %.6f\n" etapes.(6) valeurs_realtime.(6) valeurs_utime.(6) valeurs_stime.(6);
      Printf.fprintf channel "%s                   |  %.6f  |  %.6f  |  %.6f\n" etapes.(7) valeurs_realtime.(7) valeurs_utime.(7) valeurs_stime.(7);

      Printf.fprintf channel "%s         |  %.6f  |  %.6f  |  %.6f\n" etapes.(8) valeurs_realtime.(8) valeurs_utime.(8) valeurs_stime.(8);
      Printf.fprintf channel "%s      |  %.6f  |  %.6f  |  %.6f\n" etapes.(9) valeurs_realtime.(9) valeurs_utime.(9) valeurs_stime.(9);
      Printf.fprintf channel "%s         |  %.6f  |  %.6f  |  %.6f\n" etapes.(10) valeurs_realtime.(10) valeurs_utime.(10) valeurs_stime.(10);
      Printf.fprintf channel "%s               |  %.6f  |  %.6f  |  %.6f\n" etapes.(11) valeurs_realtime.(11) valeurs_utime.(11) valeurs_stime.(11);

      Printf.fprintf channel "%s    |  %.6f  |  %.6f  |  %.6f\n" etapes.(12) valeurs_realtime.(12) valeurs_utime.(12) valeurs_stime.(12);
      Printf.fprintf channel "%s |  %.6f  |  %.6f  |  %.6f\n" etapes.(13) valeurs_realtime.(13) valeurs_utime.(13) valeurs_stime.(13);
      Printf.fprintf channel "%s    |  %.6f  |  %.6f  |  %.6f\n" etapes.(14) valeurs_realtime.(14) valeurs_utime.(14) valeurs_stime.(14);
      Printf.fprintf channel "%s          |  %.6f  |  %.6f  |  %.6f\n" etapes.(15) valeurs_realtime.(15) valeurs_utime.(15) valeurs_stime.(15);

      Printf.fprintf channel "\nTOTAL:";
      Printf.fprintf channel "\n Elaboration:                |  %.6f  |  %.6f  |  %.6f" (addR 0) (addU 0) (addS 0);
      Printf.fprintf channel "\n Reconstruction:             |  %.6f  |  %.6f  |  %.6f" (addR 1) (addU 1) (addS 1);
      Printf.fprintf channel "\n Abstraction:                |  %.6f  |  %.6f  |  %.6f" (addR 2) (addU 2) (addS 2);
      Printf.fprintf channel "\n Check:                      |  %.6f  |  %.6f  |  %.6f\n" (addR 3) (addU 3) (addS 3);
      Printf.fprintf channel "\n Normalisation:              |  %.6f  |  %.6f  |  %.6f\n" valeurs_realtime.(16) valeurs_utime.(16) valeurs_stime.(16)
    end

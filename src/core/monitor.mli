(** Timing utilities for monitoring the execution time of functions.

    @author Dimitri Kirchner
    @author Marc-Antoine Ouimet *)

(** The type of labelled record for accumulating execution times. *)
type timer

(** The flag for enabling execution time monitoring in calls to {!timer}. *)
val on : bool ref

(** The flag for enabling execution time monitoring in calls to {!timer} and
    saving the statistics to the file ["./time.txt"]. *)
val onf : bool ref

(** [timer t f] is [f ()], with its execution time added to [t]. *)
val timer : timer * (unit -> 'a) -> 'a

(** [print_timers ()] prints the execution time statistics:

    - to the standard output if [!on]
    - to the file ["./time.txt"] if [Bool.not !on && !onf] *)
val print_timers : unit -> unit

(** {1 Timers} *)

val type_abbrev_kind_check : timer

val type_abbrev_type_check : timer

val ctype_elaboration : timer

val ctype_abstraction : timer

val ctype_check : timer

val datatype_constant_type_elaboration : timer

val datatype_constant_type_abstraction : timer

val datatype_constant_type_check : timer

val codatatype_constant_type_elaboration : timer

val codatatype_constant_type_abstraction : timer

val codatatype_constant_type_check : timer

val type_elaboration : timer

val type_abstraction : timer

val type_check : timer

val function_type_elaboration : timer

val function_type_abstraction : timer

val function_type_check : timer

val function_elaboration : timer

val function_abstraction : timer

val function_check : timer

val constant_elaboration : timer

val constant_abstraction : timer

val constant_check : timer

val normalisation : timer

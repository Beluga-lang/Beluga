(* Twelf.chatter := 0; *)
(* Twelf.chatter := 1; *)
(* Twelf.chatter := 2; *)

Twelf.chatter := 3;
Twelf.OS.chDir "examples/tabled";
Twelf.doubleCheck := true;

fun test (file) =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;


test "tests/tab.cfg";
test "cr/tab.cfg";
test "subtype1/tab.cfg";
test "subtype/tab.cfg";
test "refine/tab.cfg";
test "parsing/foll.cfg";
test "parsing/arithml.cfg";
test "parsing/tab.cfg";
test "mini-ml/tab.cfg";

Twelf.Table.strengthen := true;

test "seqCalc/tab-at.cfg";
test "seqCalc/tab-fol.cfg";
test "seqCalc/foc.cfg";

Twelf.OS.chDir "../..";

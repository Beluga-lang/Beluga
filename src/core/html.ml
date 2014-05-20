type htmlClass = Kind | Const | None | Fun
let genHtml = ref false
let indent = ref 0
let ids = ref []

let spacess : string =	String.make (!indent) ' '

let page = ref ""

let header =
	"<head>
	\n\t<style type=\"text/css\">
	\n\t\tbody {
	\n\t\t\tpadding: 2em 1em 2em 1em;
	\n\t\t\tmargin: 0;
	\n\t\t\tfont-family: sans-serif;
	\n\t\t\tcolor: black;
	\n\t\t\tbackground: white;}
	\n\t\t:link { color: #00C; background: transparent }
	\n\t\t:visited { color: #00C; background: transparent }
	\n\t\ta:active { color: #C00; background: transparent }
	\n\t\t.keyword { color: #FF0000; background: transparent }
	\n\t</style>
	\n</head>\n"

let generatePage filename = 
begin
	let oc = open_out filename in
	output_string oc header;
	output_string oc "<body>\n";
	output_string oc  (!page ^ "\n");
	output_string oc "</body>\n" ;
	close_out oc
end

let appendAsAnchor innerHtml id htmlClass =
	ids := id :: !ids ;
	page := (!page) ^ "\n" ^ spacess ^ "<span id=" ^ id ^ 
			(match htmlClass with
				| Kind -> " class=kind "
				| Const -> " class=const "
				| Fun -> " class=fun "
				| _ -> "")
			^ ">" ^ innerHtml ^ "</span>\n"

(* let appendAsLink innerHtml id =
	page := (!page) ^ "\n" ^ spacess ^ "<a href=#" ^ id ^ ">" ^ innerHtml ^ "</a>" *)

let append innerHtml =
	page := (!page) ^ "\n" ^ spacess ^ "<span>" ^ innerHtml ^ "</span>"




(********************
	TODO:
		- make constructor names bold / other color?
		- add linking within pages



*)
(* let turnstile = '⊢'

let arrow = '→'

let arrow2 = '⇒'

let fix str =
	let aux s c1 c2 i c = 
		if c = c1 && str.[i+1] = c2 then
		str.[i] <- s ; str.[i+1] <- ' ' 
	in
	String.iteri (aux '⊢' '|' '-') str ;
	String.iteri (aux '→' '-' '>') str ;
	String.iteri (aux '⇒' '=' '>') str ;
	str
	let _ = String.iteri (fun i c -> if c = '|' && s.[i+1] = '-' then (String.set s i '⊢' ; String.set s (i+1) ' ')) s in
	let _ = String.iteri (fun i c -> if c = '-' && s.[i+1] = '>' then (let _ = String.set s i  '→' in let _ = String.set s (i+1)  ' ' in ())) s in
	let _ = String.iteri (fun i c -> if c = '=' && s.[i+1] = '>' then (let _ = String.set s i  '⇒' in let _ = String.set s (i+1)  ' ' in ())) s in
	str *)
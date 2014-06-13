type htmlClass = Kind | Const | None | Fun
let genHtml = ref false
let printingHtml = ref false

let page = ref ""

let header =
"<head>" ^
"\n\t<style type=\"text/css\">" ^
"\n\t\tbody {" ^
"\n\t\t\tpadding: 2em 1em 2em 1em;" ^
"\n\t\t\tmargin: 0;" ^
"\n\t\t\tfont-family: sans-serif;" ^
"\n\t\t\tcolor: black;" ^
"\n\t\t\tbackground: white;}" ^
"\n\t\ta{text-decoration:none;}"^
"\n\t\ta:link { color: #00C; background: transparent }" ^
"\n\t\t:visited { color: #00C; background: transparent }" ^
"\n\t\ta:active { color: #C00; background: transparent }" ^
"\n\t\tkeyword { color: #3333cc ; background: transparent }" ^
"\n\t\tcode { display:block; background-color: #dddddd;border: 1px dashed maroon; color: black;font-family: \"courier\";padding:5px;margin:0; }" ^
"\n\t\t.typ {color: #660000; font-weight:bold}" ^
"\n\t\t.constructor {color: #335C85; font-weight:bold}" ^
"\n\t\t.function {color: #660033; font-weight:bold}" ^
"\n\t</style>\t" ^
"</head>\n"

let generatePage filename = 
begin
	(* Merge different code blocks into, as long as there isn't anything inbetween *)
	let fixCodeRegex = Str.regexp "</code>\\(\\([\r\n\t]\\|<br>\\)*?\\)<code>" in
	let page = Str.global_replace fixCodeRegex "\\1" !page in

	(* Output the HTML file *)
	let oc = open_out filename in
	output_string oc header;
	output_string oc "<body>\n";
	output_string oc  (page ^ "\n");
	output_string oc "</body>\n" ;
	close_out oc
end

let replaceNewLine = Str.global_replace (Str.regexp_string "\n") "<br>"

let append innerHtml =
	let innerHtml = replaceNewLine innerHtml in
	page := (!page) ^ "\n"  ^ "<br><code>" ^ innerHtml ^ "</code>"

let appendAsComment innerHtml = 
	let innerHtml = Str.global_replace (Str.regexp "\\(%{\\|}%\\)") "" innerHtml in
	let innerHtml = replaceNewLine innerHtml in
	page := (!page) ^ "\n" ^ "<p>" ^ innerHtml ^ "</p>"

(********************
	TODO:
		- make constructor names bold / other color?
		- add linking within pages



*)
(* let turnstile = '⊢'

let arrow = '→'

let arrow2 = '⇒'*)
let genHtml = ref false
let printingHtml = ref false
let genCSS = ref true
let page = ref ""


(* display:block; border: 1px dashed maroon;
 *)
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
"\n\t\ta:visited { color: #00C; background: transparent }" ^
"\n\t\ta:active { color: #C00; background: transparent }" ^
"\n\t\tkeyword { color: #3333cc ; background: transparent }" ^
"\n\t\tp {display: inline;}"^
"\n\t\tpre {"^
"\n\t\t\tborder: 1px dashed maroon;  display:block; "^
"\n\t\t\tpadding:8px; background-color: #dddddd;}" ^
"\n\t\tcode {" ^
"\n\t\t\tbackground-color: #dddddd;"^
"\n\t\t\tcolor: black; font-family: \"courier\";margin:0; "^
"\n\t\t\twhite-space: pre-wrap; }" ^
"\n\t\t.typ {color: #660000; font-weight:bold}" ^
"\n\t\t.constructor {color: #335C85; font-weight:bold}" ^
"\n\t\t.function {color: #660033; font-weight:bold}" ^
"\n\t\t.schema {color: #6600CC; font-weight:bold}" ^
"\n\t</style>\t" ^
"</head>\n"

let generatePage filename = 
begin
	(* Merge different code blocks into, as long as there isn't anything inbetween *)
	let fixCodeRegex = Str.regexp "</code></pre>\\(\\([\r\n\t]\\|<br>\\)*?\\)<pre><code>" in
	let page = Str.global_replace fixCodeRegex "\\1" !page in

	(* Output the HTML file *)
	let oc = open_out filename in
	if !genCSS then begin
		output_string oc header;
		output_string oc "<body>\n";
		output_string oc  (page ^ "\n");
		output_string oc "</body>\n" ;
	end else
		output_string oc  (page ^ "\n");
	close_out oc
end

let replaceNewLine = Str.global_replace (Str.regexp "[\n]") "<br>"

let append innerHtml =
	page := (!page) ^ "<br><pre><code>" ^ innerHtml ^ "</code></pre>"

let appendAsComment innerHtml = 
	let innerHtml = Str.global_replace (Str.regexp "\\(%{\\|}%\\)") "" innerHtml in
	let innerHtml = replaceNewLine innerHtml in
	page := (!page) ^ "\n" ^ "<p>" ^ innerHtml ^ "</p>"

let ids = ref []

let addId s = ids := s::!ids

let idExists s = List.exists (fun x -> x=s) !ids

(* let turnstile = '⊢'

let arrow = '→'

let arrow2 = '⇒'*)
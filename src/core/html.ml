type css = Normal | NoCSS | File of string

let genHtml : bool ref = ref false
let printingHtml : bool ref = ref false
let css : css ref = ref Normal
let filename : string ref = ref "out.html"
let page : Buffer.t = Buffer.create 0


(* display:block; border: 1px dashed maroon;
 *)
let header =
"<html>\n<head>" ^
"\n\t<meta charset=\"UTF-8\">" ^ 
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

let generatePage () = 
begin
  (* Merge different code blocks into, as long as there isn't anything inbetween *)
  let fixCodeRegex = Str.regexp "</code></pre>\\(\\([\r\n\t]\\|<br>\\)*?\\)<pre><code>" in
  let page = Str.global_replace fixCodeRegex "\\1" (Buffer.contents page) in

  (* Output the HTML file *)
  let oc = open_out !filename in
  let out = output_string oc in
  begin match !css with
  | NoCSS -> out  (page ^ "\n");
  | Normal -> begin
      out header;
      out "<body>\n";
      out  page;
      out "\n</body>\n</html>\n"
    end
  | File s -> begin
      out "<html>\n<head>\n\t<link rel=\"stylesheet\" type=\"text/css\" href=\"";
      out s; out "\">\n</head>\n<body>\n";
      out page;
      out "\n</body>\n</html>\n"
    end
  end;
  close_out oc
end

(* let replaceNewLine = Str.global_replace (Str.regexp "[\n]") "<br>" *)

let append innerHtml =
  Buffer.add_string page ("<br><pre><code>" ^ innerHtml ^ "</code></pre>")

let (|>) x f = f x

let appendAsComment innerHtml = 
  let from_markdown s =
       (* H3 Header -- needs to be before H2 and H1*)
       Str.global_replace (Str.regexp "^###\\([^\n]*\\)$") "<h3>\\1</h3>" s
       (* H2 Header -- needs to be before H1 *)
    |> Str.global_replace (Str.regexp "^##\\([^\n]*\\)$") "<h2>\\1</h2>"
       (* H1 Header *)
    |> Str.global_replace (Str.regexp "^#\\([^\n]*\\)$") "<h1>\\1</h1>"
       (* Inline Code *)
    |> Str.global_replace (Str.regexp "`\\([^`]*\\)`") "<code>\\1</code>"
       (* Bold -- Needs to be before italics *)
    |> Str.global_replace (Str.regexp "\\*\\*\\([^\\*]*\\)\\*\\*") "<b>\\1</b>"
       (* Italics *)
    |> Str.global_replace (Str.regexp "\\*\\([^\\*]*\\)\\*") "<i>\\1</i>"
       (* Unordered Lists *)
    |> Str.global_replace (Str.regexp "^-\\([^-]\\)\\(\\([^\n]\\|[\n][ ]\\)*\\)") "<ul><li>\\1\\2</li></ul>" 
       (* Fix Unordered Lists *)
    |> Str.global_replace (Str.regexp "</ul>\\([ \n\r]?\\)<ul>") "\\1"
       (* Ordered Lists *)
    |> Str.global_replace (Str.regexp "^[0-9]+\\.\\(\\([^\n]\\|[\n][ ]\\)*\\)") "<ol><li>\\1</li></ol>" 
       (* Fix Ordered Lists *)
    |> Str.global_replace (Str.regexp "</ol>\\([ \n\r]?\\)<ol>") "\\1"
       (* Two space at the end of a line for a <br> *)
    |> Str.global_replace (Str.regexp "  $") "<br>"
       (* 5+ dashes for <hr> *)
    |> Str.global_replace (Str.regexp "^-----+") "<hr>"
  in
  let innerHtml = Str.global_replace (Str.regexp_string "```") "" innerHtml in
  let innerHtml = Str.global_replace (Str.regexp_string "|-") "&#8866;" innerHtml in
  let innerHtml = from_markdown innerHtml in
  Buffer.add_string page  ("\n" ^ "<p>" ^ innerHtml ^ "</p>")

let ids = ref []

let addId s = ids := s::!ids

let idExists s = List.exists (fun x -> x=s) !ids

(* let turnstile = '⊢'

let arrow = '→'

let arrow2 = '⇒'*)
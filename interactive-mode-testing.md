Interactive Mode Testing
========================

Terminology:

* `beluga-mode` refers to the Emacs code that interfaces with the interactive
  mode.
* _The interactive mode_ refers to the interactive prompt you get when you run
  `beluga -I` (and optionally with `-emacs`, which just suppresses certain
  helpful human-intended output.)
  
To test the interactive mode, we use a _test transcript_, with the following
format:

1. _Input text:_ the test transcript should begin with the program text to
   test. This text will be available as `input.bel`, so typically the first
   _interaction_ that will follow the input text will be
   ```
   %:load input.bel
   - The file input.bel has been successfully loaded;
   ```
   Formally, the input text is any sequence up bytes up to the string `%:`
   appearing *at the beginning of a line*.
2. _Interactions:_ There are be one or more such clauses, and they
   take the form:
   ```
   %:command
   response
   ```
   The response indicated in the transcript is the *expected response*, and will
   be checked against the actual output from Beluga.
   If the output matches, then the output is written to the file
   `last-output.bel`; this allows the subsequent command to use the output of
   the previous command, e.g. to fill a hole with the output of a split.
   

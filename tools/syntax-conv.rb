#!/usr/bin/env ruby
# -*- coding: utf-8 -*-

class String
  def gsub_ignore_comments!(pat, *replacement, &block)
    src = pat.source.gsub /\\s/, '(?-m:\s|%.*$)'
    pat = Regexp.new("(?:(?<comment>(?m:%\{.*?\}%)|%.*?$)|#{src})", pat.options)
    current, post = "", self
    while pat =~ post do
      pre, s, post = $`, $&, $'
      s.gsub!(pat, *replacement, &block) unless $~[:comment]
      current <<= pre << s
    end
    self.replace (current << post)
  end
end

class Block
  attr_reader :content

  def initialize(content)
    @content = content
  end

  def mogrify!() self end
end

class CompBlock < Block

  def mogrify!()
    # Temporarily translate '..' into its unicode version, to more easily distinguish it from '.'.
    content.gsub! /\.\./, '…'
    content.gsub! /->/, '→'
    content.gsub! /<-/, '←'
    content.gsub! /\=>/, '⇒'
    content.gsub! /\\([[:word:]]+)\./ do |s|
      "\\" + $1 + "__LAMDOT__"
    end

    # schema declarations
    content.gsub_ignore_comments! /schema\s.*?;/m do |s|
      s.gsub_ignore_comments! /\./, ','
      s.gsub /((?:block\s|,)\s*)([^,;\[\]]+)/m do |s|
        s.gsub /^((?:block\s|,)\s*)([^:]+)$/m, '\1_t:\2'
      end
    end

    # block expressions
    content.gsub_ignore_comments! /block\s[^;]*?\]/m do |s|
      s.gsub_ignore_comments! /\./, ','
      s.gsub! /((?:block\s|,)\s*)([^,;\[\]]+)/m do |s|
        s.gsub /^((?:block\s|,)\s*)([^:]+)$/m, '\1_t:\2'
      end
    end

    # rec signature
    content.gsub_ignore_comments! /^(rec|let|and)\s.*?[^[[:word:]]]=/m do |s|
      s.gsub_ignore_comments! /(?<leadin>(::|→|:|\})\s*)\(?(?<obj>[^\{\}]*?)\)?\s*\[\s*(?<ctx>[^\.]*?)\s*\]/m, '\k<leadin>[\k<ctx>. \k<obj>]'
      s.gsub_ignore_comments! /\{(?<leadin>\s*)(?<ctx>\s*[^\*\.\{\}:]*?:\s*)(?<ctxtyp>[^\*\.\{\}:]*?)(?<leadout>\s*)\}/m, '(\k<leadin>\k<ctx>\k<ctxtyp>\k<leadout>)'
      s.gsub_ignore_comments! /(?<leadin>\{\s*)(?<ctx>\s*[^\*\.\{\}:]*?:\s*)\((?<ctxtyp>[^\*\.\{\}:]*?)\)\*(?<leadout>\s*\})/m, '\k<leadin>\k<ctx>\k<ctxtyp>\k<leadout>'
    end

    # rec and top-level let body
    content.gsub_ignore_comments! /[^[[:word:]]]=.*?([[:space:]]and[[:space]]|;)/m do |s|
      s.gsub_ignore_comments! /\{.*?\}/m do |s|
        s.gsub_ignore_comments! /(?<leadin>(::|→|:|\})\s*)\(?(?<obj>[^\{\}]*?)\)?\s*\[\s*(?<ctx>[^\.]*?)\s*\]/m, '\k<leadin>[\k<ctx>. \k<obj>]'
      end
    end

    # types in case patterns
    content.gsub_ignore_comments! /\|.*?⇒/ do |s|
      s.gsub_ignore_comments! /(?<leadin>:\s*)\(?(?<obj>[^\{\}]*?)\)?\s*\[\s*(?<ctx>.*?)\s*\](?<leadout>\s*⇒)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    end

    content.gsub_ignore_comments! /\(\s*\[\s*(?<ctx>[^\.\[\]%]*?)\s*\]\s*(?<obj>((?<pobj>\(([^()]+|\g<pobj>)*\))|[^()])+)\s*\)/m,
                                 '[\k<ctx>. \k<obj>]'
    # let expression pattern
    content.gsub_ignore_comments! /(?<leadin>let\s+(\{.*?\}\s*)*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*=)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'

    # type annotated let expression pattern
    content.gsub_ignore_comments! /(?<leadin>let\s+(\{[^\{\}]*?\}\s*)*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]=]*?)(?<typannot>\s*:\s*[^=]*?)(?<leadout>\s*=)/m, '\k<leadin>[\k<ctx>. \k<obj>]__ANNOT__\k<typannot>__ANNOT__\k<leadout>'
    # type annotation of let expression pattern
    content.gsub! /__ANNOT__.*?__ANNOT__/ do |s|
      s.gsub_ignore_comments! /(?<leadin>(::|→|:|\})\s*)\(?(?<obj>[^\{\}]*?)\)?\s*\[\s*(?<ctx>.*?)\s*\]/m, '\k<leadin>[\k<ctx>. \k<obj>]'
      s.gsub_ignore_comments! /\{(?<leadin>\s*)(?<ctx>\s*[^\*\{\}:]*?:\s*)(?<ctxtyp>[^\*\{\}:]*?)(?<leadout>\s*)\}/m, '(\k<leadin>\k<ctx>\k<ctxtyp>\k<leadout>)'
      s.gsub_ignore_comments! /(?<leadin>\{\s*)(?<ctx>\s*[^\*\{\}:]*?:\s*)\((?<ctxtyp>[^\*\{\}:]*?)\)\*(?<leadout>\s*\})/m, '\k<leadin>\k<ctx>\k<ctxtyp>\k<leadout>'
      s.gsub! /__ANNOT__/, ''
    end

    # let expression def
    content.gsub_ignore_comments! /(?<leadin>=\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*in)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'

    # case scrutinee
    content.gsub_ignore_comments! /(?<leadin>case\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*of)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'

    # case branch lhs
    content.gsub_ignore_comments! /(?<leadin>\|\s*(\s*\{[^\{\}]*?\}\s*)*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*(:|⇒))/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'

    # case branch rhs, let expression body and if branches
    content.gsub_ignore_comments! /(?<leadin>(=>|⇒|in\s|then\s|else\s)\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>((?<pobj>\(([^()]+?|\g<pobj>)*\))|[^()])+?)(?<leadout>\s*(\)|[[:space:]]and[[:space:]]|[[:space:]]else[[:space:]]|;|\|))/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'

    # if predicate
    content.gsub_ignore_comments! /(?<leadin>if\s+\(?)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>((?<pobj>\(([^()]+?|\g<pobj>)*\))|[^()])+?)(?<leadout>\s*==)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    content.gsub_ignore_comments! /(?<leadin>==\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>((?<pobj>\(([^()]+?|\g<pobj>)*\))|[^()])+?)(?<leadout>\s*\)?\s*then)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'

    content.gsub_ignore_comments! /<(?<ctx>[^<>]*?)\.(?<obj>[^<>]*?)>/m, '[\k<ctx>.\k<obj>]'
    content.gsub_ignore_comments! /FN/, 'mlam'
    content.gsub_ignore_comments! /::/, ':'

    # Undo obfuscation by unicode.
    content.gsub! /…/, '..'
    content.gsub! /→/, '->'
    content.gsub! /←/, '<-'
    content.gsub! /⇒/, '=>'
    content.gsub! /__LAMDOT__/, '.'

    self
  end
end

if ARGV.length < 1 or ARGV.length > 2 then
    $stderr.puts "Usage: #{File.basename( $0 )} file.bel"
    exit 1
end

content = File.read ARGV.pop
block = CompBlock.new content
block.mogrify!
puts block.content

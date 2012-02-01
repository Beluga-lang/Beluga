#!/usr/bin/env ruby
# -*- coding: utf-8 -*-

class String
  def gsub_ignore_comments!(pat, *replacement, &block)
    src = pat.source.gsub /\\s/, '(?:\s|%.*?$)'
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
    content.gsub_ignore_comments! /schema\s.*?;/m do |s|
      s.gsub_ignore_comments! /\./, ','
      s.gsub! /((?:block\s|,)\s*)([^,;\[\]]+)/m do |s|
        s.gsub /^((?:block\s|,)\s*)([^:]+)$/m, '\1_t:\2'
      end
    end
    content.gsub_ignore_comments! /block\s[^;]*?\]/m do |s|
      s.gsub_ignore_comments! /\./, ','
      s.gsub! /((?:block\s|,)\s*)([^,;\[\]]+)/m do |s|
        s.gsub /^((?:block\s|,)\s*)([^:]+)$/m, '\1_t:\2'
      end
    end
    content.gsub_ignore_comments! /rec\s.*?=/m do |s|
      s.gsub_ignore_comments! /(?<leadin>(::|->|→|:|\})\s*)\(?(?<obj>[^\{\}]*?)\)?\s*\[\s*(?<ctx>.*?)\s*\]/m, '\k<leadin>[\k<ctx>. \k<obj>]'
      s.gsub_ignore_comments! /\{(?<leadin>\s*)(?<ctx>\s*[^\*\{\}:]*?:\s*)(?<ctxtyp>[^\*\{\}:]*?)(?<leadout>\s*)\}/m, '(\k<leadin>\k<ctx>\k<ctxtyp>\k<leadout>)'
      s.gsub_ignore_comments! /(?<leadin>\{\s*)(?<ctx>\s*[^\*\{\}:]*?:\s*)\((?<ctxtyp>[^\*\{\}:]*?)\)\*(?<leadout>\s*\})/m, '\k<leadin>\k<ctx>\k<ctxtyp>\k<leadout>'
    end
    content.gsub_ignore_comments! /(=.*?;)/m do |s|
      s.gsub_ignore_comments! /\{.*?\}/m do |s|
        s.gsub_ignore_comments! /(?<leadin>(::|->|→|:|\})\s*)\(?(?<obj>[^\{\}]*?)\)?\s*\[\s*(?<ctx>.*?)\s*\]/m, '\k<leadin>[\k<ctx>. \k<obj>]'
      end
    end
    content.gsub_ignore_comments! /\|.*?=>/ do |s|
      s.gsub_ignore_comments! /(?<leadin>:\s*)\(?(?<obj>[^\{\}]*?)\)?\s*\[\s*(?<ctx>.*?)\s*\](?<leadout>\s*=>)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    end
    content.gsub_ignore_comments! /\(\s*\[\s*(?<ctx>[^\.]*?)\s*\]\s*(?<obj>((?<pobj>\(([^()]+|\g<pobj>)*\))|[^()])+)\s*\)/m,
                                 '[\k<ctx>. \k<obj>]'
    content.gsub_ignore_comments! /(?<leadin>let\s+(\{.*?\}\s*)*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*=)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    content.gsub_ignore_comments! /(?<leadin>=\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*in)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    content.gsub_ignore_comments! /(?<leadin>case\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*of)/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    content.gsub_ignore_comments! /(?<leadin>\|\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*(:|=>))/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    content.gsub_ignore_comments! /(?<leadin>(=>|in\s)\s*)\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*(;|\|))/m, '\k<leadin>[\k<ctx>. \k<obj>]\k<leadout>'
    # content.gsub_ignore_comments! /\[\s*(?<ctx>[^\.\[\]%]*)\s*\]\s*(?<obj>[^\[\]]*?)(?<leadout>\s*(;|=>|=|:|\|))/m, '[\k<ctx>. \k<obj>]\k<leadout>'
    content.gsub_ignore_comments! /<(?<ctx>[^<>]*?)\.(?<obj>[^<>]*?)>/m, '[\k<ctx>.\k<obj>]'
    content.gsub_ignore_comments! /FN/, 'mlam'
    content.gsub_ignore_comments! /::/, ':'
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

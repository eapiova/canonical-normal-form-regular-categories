\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{sstt-2026-abstract}[2026/03/01 SSTT 2026 abstract class]
%% a small customisation of amsart to ensure consistent formatting of abstracts, and facilitate compilation into book of abstracts
%% for SSTT 2026 Ljubljana https://ul-fmf.github.io/mfps-sstt-2026//sstt/
%% tested under TeXLive 2024, 2025, 2026
%% Peter LeFanu Lumsdaine <p.l.lumsdaine@math.su.se>

\LoadClass[11pt]{amsart}

%% Text handling and layout
\RequirePackage[T1]{fontenc}
\RequirePackage[provide=*,main=english]{babel}
\RequirePackage[babel]{csquotes}
\RequirePackage{enumitem}
\RequirePackage[a4paper,textwidth=360pt,centering,textheight=595.8pt]{geometry}
\RequirePackage{lipsum}

%% Bibliography handling
\RequirePackage[style=alphabetic]{biblatex}
\renewcommand*{\bibfont}{\normalfont\footnotesize}

%% General math packages:
\RequirePackage{amsthm,amsfonts,amsmath,amssymb}
\RequirePackage{mathtools,eucal}

%% Diagrams, logical inference rules
\RequirePackage{tikz,tikz-cd,quiver}
\RequirePackage{mathpartir}

%% Hyperref
\RequirePackage[svgnames]{xcolor}
\RequirePackage[colorlinks=true,allcolors=DarkBlue]{hyperref}

%% If theorem types needed, add them in “extra commands”
\theoremstyle{plain}
\newtheorem{theorem}{Theorem}
\newtheorem*{theorem*}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem*{lemma*}{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem*{proposition*}{Proposition}
\newtheorem{fact}[theorem]{Fact}
\newtheorem*{fact*}{Fact}
\newtheorem{conjecture}[theorem]{Conjecture}
\newtheorem*{conjecture*}{Conjecture}

\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem*{definition*}{Definition}

%% Abstract title/author commands
\newcommand{\abstracttitle}[1]{\title{#1}}
\newcommand{\abstractspeaker}[1]{\author{\textbf{#1}}}
\newcommand{\abstractcoauthor}[1]{\author{#1}}
\AtBeginDocument{\maketitle \thispagestyle{empty}}

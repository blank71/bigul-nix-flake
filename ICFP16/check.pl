#!/usr/bin/perl

use strict;
use warnings;
use IO::Handle qw(flush);

# environment
my $haskelldir = '../../bigul-dev/Haskell';
my $paperdir = `pwd`;
chomp $paperdir;

# execution
my $extensions = '-XTemplateHaskell -XTypeFamilies -XTypeOperators';
my $eval = "cabal exec -- ghc $extensions -e";

# contents
my $prompt = qr|@@>@@|;
my $newline = qr|@@\\lstcontinueline@@|;

# result
my $examples = 0;
my $wrong = 0;

# internals
my $state = 0;
my $expr = '';
my $res = '';
my $i = 0;

# file parsing
while (<STDIN>) {
  chomp;
  my $line = $_;
 
  if ($line =~ /^$prompt\s*(.*?)\s*$newline\s*$/) {
    $expr = $1;
    $state = 2;
  } elsif ($state == 2 and $line =~ /\s*(.*?)\s*$newline\s*$/) {
    $expr .= " $1";
  } elsif ($state == 2 and $line =~ /^\s*(.*?)\s*$/) {
    $expr .= " $1";
    $state = 1;
  } elsif ($line =~ /^$prompt\s*(.*)$/) {
    $expr = $1;
    $state = 1;
  } elsif ($state == 1 and $line =~ /^\s*(.*?)\s*$newline\s*$/) {
    $res .= "$1 ";
  } elsif ($state == 1) {
    $res .= $line;
    $res =~ s/\s\s+/ /g;
    runExample($expr, $res, $i);
    $expr = '';
    $res = '';
    $state = 0;
  }

  $i++;
}

# show final result
if (not $wrong) {
  print "Found $examples examples, all working.\n";
} else {
  print "Found $examples examples, $wrong not working.\n";
}

# run example and check if the result is the one in the example
sub runExample {
  my $e = shift;
  my $l = shift;
  my $i = shift;
  $examples++;
  # clean code
  $e = cleanCode($e);
  # informative message
  print "Checking \"$e\"";
  STDOUT->flush();
  # run example
  my $result = `cd $haskelldir; $eval "$e" $paperdir/icfp16.lhs`;
  die "\nError when evaluating expression.\n" if $?;
  chomp $result;
  # check result
  if ($result eq $l) { # OK
    print " [OK]\n";
  } else {             # NOK
    $wrong++;
    print "\n";
    print STDERR "Warning on line $i: expected result from the example does not match\n";
    print STDERR "                    the actual result of the expression.\n";
    print STDERR "    Expected result: $l\n";
    print STDERR "    Actual result:   $result\n";
  }
}

# clean code, removing LaTeX/lstlisting specifics
sub cleanCode {
  my $l = shift;
  $l =~ s/\@\@\|(.*?)\|\@\@/$1/gr;
}

1;

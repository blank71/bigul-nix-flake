#!/usr/bin/perl

use strict;
use warnings;
use IO::Handle qw(flush);

# environment
my $haskelldir = '../../bigul-clone/Haskell';
my $paperdir = `pwd`;
chomp $paperdir;

# execution
my $eval = 'stack ghc --';
my $extensions = '-XTemplateHaskell -XTypeFamilies -XTypeOperators';

# contents
my $prompt = qr|@@>@@|;
my $newline = qr|@@\\lstcontinueline@@|;

# result
my $examples = 0;
my $wrong = 0;

# internals
my $state = 0;
my $expr = '';
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
  } elsif ($state == 1) {
    runExample($expr, $line, $i);
    $expr = '';
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
  # informative message
  print "Checking \"$e\"";
  STDOUT->flush();
  # run example
  my $result = `cd $haskelldir; $eval $extensions -e "$e" $paperdir/icfp16.lhs`;
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

1;

#!c:\perl\bin\perl.exe -w
#=============================================================================
#   @(#)$Id$
#-----------------------------------------------------------------------------
#   Web-CAT Curator: execution script for Free Pascal submissions
#
#   usage:
#       executePascal.pl <properties-file>
#=============================================================================
use strict;
use English;
use File::stat;
use File::Copy;
use Win32::Job;
use Config::Properties::Simple;
use Web_CAT::Beautifier;

#=============================================================================
# Bring command line args into local variables for easy reference
#=============================================================================
my $propfile    = $ARGV[0];	# property file name
my $cfg         = Config::Properties::Simple->new( file => $propfile );

my $pid         = $cfg->getProperty( 'userName' );
my $working_dir	= $cfg->getProperty( 'workingDir' );
my $script_home	= $cfg->getProperty( 'scriptHome' );
my $log_dir	= $cfg->getProperty( 'resultDir' );
my $timeout	= $cfg->getProperty( 'timeoutForOneRun', 30 );


#-------------------------------------------------------
# In the future, these could be set via parameters set in Web-CAT's
# interface
#-------------------------------------------------------
my $debug              =  $cfg->getProperty( 'debug', 0 );
my $max_score          = $cfg->getProperty( 'max.score.correctness', 0 );
my $hintsLimit         = $cfg->getProperty( 'hintsLimit', 3 );
my $predicateList      = $cfg->getProperty( 'predicateList', "" );
if ( !defined( $predicateList ) || $predicateList eq "" )
{
    print STDERR "predicateList is undefined.\n";
}


#-------------------------------------------------------
# In addition, some local definitions within this script
#-------------------------------------------------------
my $script_log_relative      = "execute-script-log.txt";
my $script_log               = "$log_dir/$script_log_relative";
my $test_input_relative      = "tests-in.txt";
my $test_input               = "$log_dir/$test_input_relative";
my $instr_output_relative    = "instr-out.txt";
my $instr_output             = "$log_dir/$instr_output_relative";
my $student_output_relative  = "output.txt";
my $student_output           = "$log_dir/$student_output_relative";
my $student_rpt_relative     = "student-tdd-report.txt";
my $student_rpt              = "$log_dir/$student_rpt_relative";
my $instr_rpt_relative       = "instr-tdd-report.txt";
my $instr_rpt                = "$log_dir/$instr_rpt_relative";
my $assessment_relative      = "TDD-assessment.txt";
my $assessment               = "$log_dir/$assessment_relative";

my $student_src              = "";

my $can_proceed              = 1;
my $timeout_occurred         = 0;
my @student_eval             = ();
my @instr_eval               = ();
my $student_tests            = ""; # test case file
my $coverage                 = "0 0 1";
# my @beautifierIgnoreFiles = ( '.java' );

# From tddpas.pl
#-----------------------------
my $version         = "1.6";
my @labels          = ();	# User-provided test case names
my @test_cases	    = ();	# test case input
my @expected_output = ();	# corresponding expected output
my @case_nos        = ();       # test case number for each output line
my $delete_temps    = 0;        # Change to 0 to preserve temp files


# Prolog interpreter to use
#-----------------------------
my $prolog = "C:\\Progra~1\\SWI-Prolog\\bin\\plcon.exe";
if ( ! -x $prolog )
{
    $prolog = "G:\\SWI-Prolog\\bin\\plcon.exe";
    if ( ! -x $prolog )
    {
	die "Cannot identify correct prolog interpreter ($prolog)";
    }
}


#=============================================================================
# Locate reference implementation
#=============================================================================
# instructorReference
my $scriptData = $cfg->getProperty( 'scriptData', '.' );
#my @scriptDataDirs = < $scriptData/* >;
$scriptData =~ s,/$,,;

sub findScriptPath
{
    my $subpath = shift;
    my $target = "$scriptData/$subpath";
#    foreach my $sddir ( @scriptDataDirs )
#    {
#	my $target = $sddir ."/$subpath";
#	#print "checking $target\n";
	if ( -e $target )
	{
	    return $target;
	}
#    }
    die "cannot file user script data file $subpath in $scriptData";
}

# instructorReference
my $instr_src;
{
    my $reference = $cfg->getProperty( 'instructorReference' );
    if ( defined $reference && $reference ne "" )
    {
	$instr_src = findScriptPath( $reference );
    }
}
if ( !defined( $instr_src ) )
{
    die "Instructor reference not set.";
}
elsif ( ! -f $instr_src )
{
    die "Instructor reference '$instr_src' not found.";
}


#=============================================================================
# Script Startup
#=============================================================================
# Change to specified working directory and set up log directory
chdir( $working_dir );

sub studentLog
{
    open( SCRIPT_LOG, ">>$script_log" ) ||
	die "cannot open $script_log: $!";
    print SCRIPT_LOG @_;
    close( SCRIPT_LOG );
}


#=============================================================================
# Find the test suite file to use
# Extensions supported *.txt, *.text, *.tst, *.test
#=============================================================================
my @sources = (<*.txt *.text *.tst *.test>);
if ( $#sources < 0 || ! -f $sources[0] )
{
    studentLog ( "<p>Cannot identify a test suite file.  Did you \n",
		 "use a .txt, .text, .tst, or .test extension?</p>\n" );
    $can_proceed = 0;
}
else
{
    $student_tests = $sources[0];
    if ( $#sources > 0 )
    {
	studentLog(
	    "<p>Multiple test suite files present.  Using $student_tests.\n",
	    "Ignoring other .txt/.text/.tst/.test files.</p>\n" );
    }
}

@sources = (<*.plg *.pro *.prolog *.pl>);
if ( $#sources < 0 || ! -f $sources[0] )
{
    studentLog(	"<p>Cannot identify a Prolog source file.\n",
		"Did you use the correct extension (.plg, .pro, ",
		".prolog, or .pl)?</p>\n" );
    $can_proceed = 0;
}
else
{
    $student_src = $sources[0];
    if ( $#sources > 0 )
    {
	studentLog( "<p>Multiple Prolog source files present.  Using ",
		    "$student_src.\nIgnoring other Prolog files.</p>\n" );
    }
}


if ( $can_proceed && -d "$script_home/local" )
{
    foreach my $f ( <$script_home/local/*> )
    {
	my $newf = $f;
	$newf =~ s,^\Q$script_home/local/\E,,;
	print "copy( $f, $newf );\n" if $debug;
	copy( $f, $newf );
#	push( @beautifierIgnoreFiles, $newf );
    }
}



#=============================================================================
# A subroutine for normalizing output lines before comparing them
#=============================================================================
sub normalize
{
    my $line = shift;
    $line =~ s/^\s+//o;		# Trim leading space
    $line =~ s/\s+$//o;		# Trim trailing space
    $line =~ s/\s+/ /go;	# Convert multi-space sequences to one space
    $line =~ s/\(\s+/(/go;	# Eliminate spaces inside parentheses
    $line =~ s/\)\s+/)/go;	# Eliminate spaces inside parentheses
    #$line =~ tr/A-Z/a-z/;	# Convert to lower case
    return $line;
}

sub is_ref_test
{
    my $test_in = shift;
    return $test_in =~ m/^\s*($predicateList)\(/io;
}


#=============================================================================
# A subroutine for executing a program/collecting the output
#=============================================================================
sub run_test
{
    my $pgm          = shift;
    my $temp_input   = shift;
    my $name         = shift;
    my $title        = shift;
    my $outfile      = shift;
    my $resultfile   = shift;
    my $show_details = shift;

# Produce stdin input file for programs to use:
open( INFILE, "> $temp_input" ) ||
    die "Cannot open '$temp_input': $!";
print INFILE<<EOF;
/* send error messages to current output */
message_hook( _, silent,        _ ) :- !.
message_hook( _, informational, _ ) :- !.
message_hook( _, banner,        _ ) :- !.
message_hook( _Term, Level, OrigLines ) :-
    strip_stream_refs( OrigLines, Lines ),
    '\$messages':prefix(Level, LinePrefix, _ ), !,
    current_output( Stream ),
    print_message_lines( Stream, LinePrefix, Lines ).
strip_stream_refs( [], [] ).
strip_stream_refs( ['Stream ~w:~d: '-[_Stream, Line] | Rest ],
		   [ '$pgm:', Line, ': ' | Stripped_Rest ] ) :-
    integer( Line ),
    Line >= 0, !,
    strip_stream_refs( Rest, Stripped_Rest ).
strip_stream_refs( ['Stream ~w:~d: '-_ | Rest ],
		   [ '$pgm: ' | Stripped_Rest ] ) :-
    strip_stream_refs( Rest, Stripped_Rest ).
strip_stream_refs( [ H | Rest ], [ H | Stripped_Rest ] ) :-
    strip_stream_refs( Rest, Stripped_Rest ).
error_output( Label, N, Error, Output ) :-
    message_to_string( Error, Message_String ), !,
    string_to_atom( Message_String, Message_Atom ),
    concat( 'ERROR: ', Message_Atom, Message ),
    testcase_output( Label, N, Message, Output, [] ).

make_readable( Var, [ Name=Binding | More_Bindings ], VarName ) :-
    var( Var ),
    ( Var == Binding, Name = VarName ;
      make_readable( Var, More_Bindings, VarName ) ).
make_readable( Var=Exp, Bindings, VarName=Exp ) :-
    make_readable( Var, Bindings, VarName ).
make_readable( [], _Bindings, [] ).
make_readable( [ H | T ], Bindings, [ NewH | NewT ] ) :-
    make_readable( H, Bindings, NewH ),
    make_readable( T, Bindings, NewT ).

contained_in_free_vars( [], _ ).
contained_in_free_vars( [ Var=_ | More ], List ) :-
    member( Var=_, List ),
    contained_in_free_vars( More, List ).

write_expected_output( [] ) :-
    write( '[fail]' ), !.
write_expected_output( [[]] ) :-
    write( '[true]' ), !.
write_expected_output( T ) :-
    write( T ).

prologTDDPlugin_normalize(X, X).

prologTDDPlugin_normalize_list([], []).
prologTDDPlugin_normalize_list([H | R], [Hnorm | Rnorm]) :-
    prologTDDPlugin_normalize(H, Hnorm),
    prologTDDPlugin_normalize_list(R, Rnorm).
prologTDDPlugin_normalize_list(L, Lnorm) :-
    L \= [_|_], L\= [], prologTDDPlugin_normalize(L, Lnorm).


expected_output_takeout( X, [ Z | R ], R ) :-
    prologTDDPlugin_normalize_list(X, Xnorm),
    prologTDDPlugin_normalize_list(Z, Znorm),
    ( is_list( Xnorm ), is_list( Znorm ) ->
       intersection( Xnorm, Znorm, Xnorm ); Znorm = Xnorm ), !.
expected_output_takeout( X, [ Z1 | R ], [ Z2 | S ] ) :-
    prologTDDPlugin_normalize(Z1, Znorm),
    prologTDDPlugin_normalize(Z2, Znorm),
    expected_output_takeout( X, R, S ).
expected_output_equivalent( [], [] ).
expected_output_equivalent( [ X | R ], S ) :-
    expected_output_takeout( X, S, T ),
    expected_output_equivalent( R, T ).

testcase_output( Label, N, Output, [ Expected, Free ] ) :-
    atom_to_term( Expected, Unsorted_Term, Bindings ),
    sort( Unsorted_Term, Term ),
    sort( Free, Free_Sorted ),
    sort( Bindings, Bindings_Sorted ),
    ( contained_in_free_vars( Bindings_Sorted, Free_Sorted ) ->
      testcase_output( Label, N, Output, Term, Bindings ) ;
      write( 'F' ), nl,
      write( 'case ' ), write( N ), write( ' FAILED: ' ), write( Label ), nl,
      catch( ( make_readable( Expected, Bindings, Output_As_Atom ) ;
             Output_As_Atom = Expected ),
           _Exception,
           Output_As_Atom = Expected
      ),
      write( '  Expected: ' ), write_expected_output( Output_As_Atom ), nl,
      write( '       Got: ' ), write( 'ERROR: ' ),
      write( 'free variables not in the input appear in the output' ), nl
    ).
testcase_output( _Label, _N, [],     [fail], _Bindings ) :- write( '.' ).
testcase_output( _Label, _N, [[]],   [true], _Bindings ) :- write( '.' ).
testcase_output( _Label, _N, Output, Expected, _Bindings ) :-
    expected_output_equivalent( Output, Expected ),
    write( '.' ).
testcase_output( Label,   N, Output, Expected, Bindings ) :-
    catch( ( make_readable( Expected, Bindings, Output_As_Atom ) ;
             Output_As_Atom = Expected ),
           _Exception,
           Output_As_Atom = Expected
    ),
    write( 'F' ), nl,
    write( 'case ' ), write( N ), write( ' FAILED: ' ), write( Label ), nl,
    write( '  Expected: ' ), write_expected_output( Output_As_Atom ), nl,
    write( '       Got: ' ), write_expected_output( Output ), nl.

testcase( Label, N, Case, Expected ) :-
    catch(
	(
	    atom_to_term( Case, Predicate, Bindings ),
	    % write( Bindings ), nl,
	    % write( Predicate ), nl, nl,
	    ( setof( Bindings, Predicate, Solutions ) ; Solutions = [] ),
	    testcase_output( Label, N, Solutions, [ Expected, Bindings ] )
	),
	Exception,
	error_output( Label, N, Exception, Expected )
    ).
testcase( N, Case, Expected ) :-
    testcase( Case, N, Case, Expected ).

?- set_feature( debug_on_error, false ),
   tell( '$outfile' ).

/* Load given input file, bail if any problems arise */
% ?- load_files( ['$pgm'], [silent(true)] ).
?- ['$pgm'].
?- style_check( [ -singleton, -atom ] ).

/* Run test cases one at a time using testcase/2 */
EOF
# to counteract the ' in the output above, for emacs
my $num_cases = 0;
for ( my $c = 0; $c <= $#test_cases; $c++ )
{
    chomp( $test_cases[$c] );
    if ( $show_details || is_ref_test( $test_cases[$c] ) )
    {
	$num_cases++;
	print INFILE "?- testcase( ";
	if ( $labels[$c] ne "" )
	{
	    print INFILE "'", $labels[$c], "', ";
	}
	print INFILE $c+1, ",\n'", $test_cases[$c], "',\n";
	print INFILE "'[\n", $expected_output[$c], "]').\n\n";
    }
}
if ( $name =~ /reference/io )
{
    print INFILE<<EOF;

/* generate coverage report */
?- report_coverage.
?- print_hints( $hintsLimit ).
EOF
}
print INFILE<<EOF;

/* Exit from Prolog when done */
?- told, halt.
EOF
close( INFILE );

    # Exec program and collect output
    my $job = Win32::Job->new;
    my $pid = $job->spawn( "cmd.exe",
			   "cmd /c $prolog -f $temp_input -t halt." );
    if ( ! $job->run( $timeout ) )
    {
	$timeout_occurred++;
    }
#    system( "$pgm < $temp_input > $outfile" );

    #=========================================================================
    # Compare the output to test case expectations
    #=========================================================================

    my $failures    = 0;    # count of failures
    my $errs        = 0;    # Number of runtime errors
    my $found_dot   = 0;

    open( STUDENT, "$outfile" ) ||
	die "Cannot open file for input '$outfile': $!";
    open( RESULT, ">$resultfile" ) ||
	die "Cannot open file for output '$resultfile': $!";

    print RESULT <<EOF;
<div class="shadow"><table><tbody>
<tr><th>$title</th></tr>
<tr><td><pre>
tddplg.pl v$version   (c) 2004 Virginia Tech. All rights reserved.
Testing $name using $student_tests

EOF
    while ( <STUDENT> )
    {
	if ( /FAILED:/o )
	{
	    $failures++;
	}
	elsif ( /ERROR:/o )
	{
	    $errs++;
	    $failures--;
	}
	elsif ( s/^coverage:\s+//o )
	{
	    chomp;
	    $coverage = $_;
	    next;
	}
	if ( /^\./o )
	{
	    $found_dot = 1;
	}
	s/(\.{78})/$1\n/go;
	print RESULT $_;
    }

    close( STUDENT );

    if ( $errs > $num_cases )
    {
	$errs = $num_cases;
    }
    if ( !$found_dot )
    {
	$failures = $num_cases - $errs;
    }
    my $succeeded = $num_cases - $failures - $errs;
    my $eval_score = ( $num_cases > 0 )
	? $succeeded/$num_cases
	: 0;
    print RESULT
	"\nTests Run: $num_cases, Errors: $errs, Failures: $failures (",
        sprintf( "%.1f", $eval_score*100 ),
        "%)\n</pre></td></tr></table></div>",
        "<div class=\"spacer\">&nbsp;</div>\n";
    close( RESULT );
    return ( $eval_score, $succeeded, $num_cases );
}


if ( $can_proceed )
{

#=============================================================================
# Phase I: Parse and split the test case input file
#=============================================================================
open ( CASES, $student_tests ) ||
    die "Cannot open '$student_tests': $!";

my $scanning_input = 0;
my $case = -1;
while ( <CASES> )
{
    # skip comment lines
    next if ( m,^//(?!--|==),o );

    if ( m,^//==,o )
    {
	if ( $scanning_input )
        {
	    studentLog( "<p>$student_tests: ", $INPUT_LINE_NUMBER - 1,
		": improperly formatted test case.</p>\n" );
        }
	my $label = $_;
	chomp $label;
	$label =~ s,^//==[-=\s]*,,o;
	$label =~ s,[-=\s]*$,,o;
	# if ( $label eq "" ) { $label = "(no label)"; }
	push( @labels, $label );
	push( @test_cases, "" );
	push( @expected_output, "" );
	$case++;
	push( @case_nos, $case );
	$scanning_input = 1;
    }
    elsif ( m,^//--,o )
    {
	if ( ! $scanning_input )
	{
	    studentLog( "<p>$student_tests: ", $INPUT_LINE_NUMBER,
			": improperly formatted test case; cannot ",
			"proceed.</p>\n" );
	}
	$scanning_input = 0;
    }
    else
    {
	if ( $scanning_input )
	{
	    # Then this is an input line
	    if ( $#test_cases < 0 )
	    {
	        studentLog( "<p>$student_tests: ", $INPUT_LINE_NUMBER,
			    ": improperly formatted test case.</p>\n" );
	    }
	    else
	    {
		s/'/\\'/go;
		$test_cases[$#test_cases] .= $_;
		if ( $labels[$#labels] eq "" )
		{
		    # Use first line of input for case label
		    chomp;
		    $labels[$#labels] = $_;
		}
	    }
	}
	else
	{
	    if ( $#labels < 0 )
	    {
		studentLog( "<p>$student_tests: ", $INPUT_LINE_NUMBER,
			    ": improperly formatted test case.</p>\n" );
	    }
	    else
	    {
		s/\b_\b/Underscore/go;
		s/'/\\'/go;
		$expected_output[$#expected_output] .= $_;
	    }
	}
    }
}
close( CASES );

if ( $#case_nos < 0 || $case_nos[$#case_nos] != $case )
{
    push( @case_nos, $case );
}
for ( my $c = 0; $c <= $#labels; $c++ )
{
    $labels[$c] =~ s/'/\\'/go;

}


#=============================================================================
# Phases II and III: Execute the program and produce results
#=============================================================================
if ( $can_proceed )
{
@student_eval = run_test( $student_src,
			  $test_input,
			  "your submission",
		  "Program Correctness (Results from Your Tests on Your Code)",
			  $student_output,
			  $student_rpt, 1 );
$cfg->setProperty( "studentEval", join( " ", @student_eval ) );

if ( $timeout_occurred )
{
	studentLog( "<p>Your program exceeded the allowable time limit.\n",
		    "This may be due to an infinite recursion problem or ",
		    "and infinite looping problem.</p>\n" );
}
elsif ( $student_eval[1] == $student_eval[2] )
{
    @instr_eval   = run_test( $instr_src,
			      $test_input,
			      "reference implementation",
      "Test Validity (Results From Your Tests on the Reference Solution)",
			      $instr_output,
			      $instr_rpt, 0 );

    if ( !$timeout_occurred )
    {
	$cfg->setProperty( "instructorEval", join( " ", @instr_eval ) );
	$cfg->setProperty( "coverage",       $coverage );
    }
    else
    {
	print STDERR "reference implementation exceeded timeout!\n";
    }
}
else
{
    studentLog( "<p>Your program must pass all of your test cases ",
		"before you can receive a non-zero score and before ",
		"the reference implementation will be run.</p>\n" );
	$cfg->setProperty( "instructorEval", "0 0 1" );
	$cfg->setProperty( "coverage",       $coverage );
#    open( ASSESSMENT, ">$assessment" ) ||
#	die "Cannot open 'coverage.txt': $!";
#    print ASSESSMENT
#	join( " ", @student_eval ), "\n",
#	"0 0 1\n",
#	"$coverage\n";
#    close( ASSESSMENT );
}

#my $beautifier = new Web_CAT::Beautifier;
#$beautifier->beautifyCwd( $cfg, \@beautifierIgnoreFiles );

}
}


#=============================================================================
# Update and rewrite properties to reflect status
#=============================================================================

my $reportCount = $cfg->getProperty( 'numReports', 0 );
if ( -f $script_log && stat( $script_log )->size != 0 )
{
    $reportCount++;
    $cfg->setProperty( "report${reportCount}.file",     $script_log_relative );
    $cfg->setProperty( "report${reportCount}.mimeType", "text/html" );
}
#if ( $can_proceed )
#{
#    $reportCount++;
#    $cfg->setProperty( "report${reportCount}.file", $student_rpt_relative );
#    $cfg->setProperty( "report${reportCount}.mimeType", "text/html" );

#    $reportCount++;
#    $cfg->setProperty( "report${reportCount}.file", $instr_rpt_relative );
#    $cfg->setProperty( "report${reportCount}.mimeType", "text/html" );

#    $reportCount++;
#    $cfg->setProperty( "report${reportCount}.file",
#		       $student_output_relative );
#    $cfg->setProperty( "report${reportCount}.mimeType", "text/plain" );
#    $cfg->setProperty( "report${reportCount}.inline",   "false" );
#    $cfg->setProperty( "report${reportCount}.label",
#		       "Your submission's output" );
#}
if ( !$can_proceed
     || $timeout_occurred
     || $student_eval[1] != $student_eval[2] )
{
    $cfg->setProperty( "score.correctness", 0 );
    if ( $timeout_occurred )
    {
	$cfg->setProperty( "timeoutOccurred", 1 );
    }
}
$cfg->setProperty( "numReports", $reportCount );
$cfg->save();

if ( $debug )
{
    my $props = $cfg->getProperties();
    while ( ( my $key, my $value ) = each %{$props} )
    {
	print $key, " => ", $value, "\n";
    }
}


#-----------------------------------------------------------------------------
exit( 0 );

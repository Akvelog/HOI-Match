package HOI::Match;

#use Alias qw(attr);

require Exporter;

use Parse::Lex;
use HOI::typeparser;

our @ISA = qw( Exporter );
our @EXPORT_OK = qw( pmatch );
our $VERSION = '0.07';

# The inline code below comes from Alias (https://metacpan.org/pod/Alias) with a patch from issue #64987 (https://rt.cpan.org/Public/Bug/Display.html?id=64987)

use Inline C => <<'END_C';

#ifndef PERL_VERSION
#include "patchlevel.h"
#define PERL_REVISION         5
#define PERL_VERSION          PATCHLEVEL
#define PERL_SUBVERSION       SUBVERSION
#endif

#ifndef GvCV_set
#define GvCV_set(gv,cv) GvCV((gv)) = (cv)
#endif

#if PERL_REVISION == 5 && (PERL_VERSION < 4 || (PERL_VERSION == 4 && PERL_SUBVERSION <= 75 ))
#define PL_stack_sp	stack_sp
#endif

void process_flag(char *varname, SV **svp, char **strp, STRLEN *lenp)
{
    GV *vargv = gv_fetchpv(varname, FALSE, SVt_PV);
    SV *sv = Nullsv;
    char *str = Nullch;
    STRLEN len = 0;

    if (vargv && (sv = GvSV(vargv))) {
	if (SvROK(sv)) {
	    if (SvTYPE(SvRV(sv)) != SVt_PVCV)
		croak("$%s not a subroutine reference", varname);
	}
	else if (SvOK(sv))
	    str = SvPV(sv, len);
    }
    *svp = sv;
    *strp = str;
    *lenp = len;
}

void attr(SV *hashref)
{
    dSP;
    HV *hv;
    int in_destroy = 0;
    int deref_call;
    
    if (SvREFCNT(hashref) == 0)
    in_destroy = 1;
    
    ++SvREFCNT(hashref);	/* in case LEAVE wants to clobber us */

    if (SvROK(hashref) &&
    (hv = (HV *)SvRV(hashref)) && (SvTYPE(hv) == SVt_PVHV))
    {
    SV *val, *tmpsv;
    char *key;
    I32 klen;
    SV *keypfx, *attrpfx, *deref;
    char *keypfx_c, *attrpfx_c, *deref_c;
    STRLEN keypfx_l, attrpfx_l, deref_l;

    //process_flag("Alias::KeyFilter", &keypfx, &keypfx_c, &keypfx_l);
    (keypfx = NULL), (keypfx_c = NULL), (keypfx_l = 0);
    process_flag("AttrPrefix", &attrpfx, &attrpfx_c, &attrpfx_l);
    //process_flag("Alias::Deref", &deref, &deref_c, &deref_l);
    (deref = NULL), (deref_c = NULL),(deref_l = 0);
    deref_call = (deref && !deref_c);
    
    LEAVE;                      /* operate at a higher level */
    
    (void)hv_iterinit(hv);
    while ((val = hv_iternextsv(hv, &key, &klen))) {
        GV *gv;
        CV *cv;
        int stype = SvTYPE(val);
        int deref_this = 1;
        int deref_objects = 0;

        /* check the key for validity by either looking at
         * its prefix, or by calling &$Alias::KeyFilter */
        if (keypfx) {
            if (keypfx_c) {
                if (keypfx_l && klen > keypfx_l
                && strncmp(key, keypfx_c, keypfx_l))
                continue;
            } else {
                //dSP;
                SV *ret = Nullsv;
                I32 i;
                
                ENTER; SAVETMPS; PUSHMARK(sp);
                XPUSHs(sv_2mortal(newSVpv(key,klen)));
                PUTBACK;
                if (perl_call_sv(keypfx, G_SCALAR))
                ret = *PL_stack_sp--;
                SPAGAIN;
                i = SvTRUE(ret);
                FREETMPS; LEAVE;
                if (!i)
                continue;
            }
        }

        if (SvROK(val) && deref) {
            if (deref_c) {
                if (deref_l && !(deref_l == 1 && *deref_c == '0'))
                deref_objects = 1;
            }
            else {
                //dSP;
                SV *ret = Nullsv;
                
                ENTER; SAVETMPS; PUSHMARK(sp);
                XPUSHs(sv_2mortal(newSVpv(key,klen)));
                XPUSHs(sv_2mortal(newSVsv(val)));
                PUTBACK;
                if (perl_call_sv(deref, G_SCALAR))
                ret = *PL_stack_sp--;
                SPAGAIN;
                deref_this = SvTRUE(ret);
                FREETMPS; LEAVE;
            }
        }
        
        /* attributes may need to be prefixed/renamed */
        if (attrpfx) {
            STRLEN len;
            if (attrpfx_c) {
                if (attrpfx_l) {
                    SV *keysv = sv_2mortal(newSVpv(attrpfx_c, attrpfx_l));
                    sv_catpvn(keysv, key, klen);
                    key = SvPV(keysv, len);
                    klen = len;
                }
            }
            else {
                //dSP;
                SV *ret = Nullsv;
                
                ENTER; PUSHMARK(sp);
                XPUSHs(sv_2mortal(newSVpv(key,klen)));
                PUTBACK;
                if (perl_call_sv(attrpfx, G_SCALAR))
                ret = *PL_stack_sp--;
                SPAGAIN; LEAVE;
                key = SvPV(ret, len);
                klen = len;
            }
        }

        if (SvROK(val) && (tmpsv = SvRV(val))) {
        if (deref_call) {
            if (!deref_this)
            goto no_deref;
        }
        else if (!deref_objects && SvOBJECT(tmpsv))
            goto no_deref;

        stype = SvTYPE(tmpsv);
        if (stype == SVt_PVGV)
            val = tmpsv;

        }
        else if (stype != SVt_PVGV) {
        no_deref:
        val = sv_2mortal(newRV(val));
        }
        
        /* add symbol, forgoing "used once" warnings */
        gv = gv_fetchpv(key, GV_ADDMULTI, SVt_PVGV);
        
        switch (stype) {
        case SVt_PVAV:
        save_ary(gv);
        break;
        case SVt_PVHV:
        save_hash(gv);
        break;
        case SVt_PVGV:
        save_gp(gv,TRUE);   /* hide previous entry in symtab */
        break;
        case SVt_PVCV:
            cv = GvCV(gv);
        SAVESPTR(cv);
        GvCV_set(gv,Null(CV*));
        break;
        default:
        save_scalar(gv);
        break;
        }
        sv_setsv((SV*)gv, val); /* alias the SV */
    }
    ENTER;			    /* in lieu of the LEAVE far beyond */
    }
    if (in_destroy)
    --SvREFCNT(hashref);	    /* avoid calling DESTROY forever */
    else
    SvREFCNT_dec(hashref);
    
    XPUSHs(hashref);                /* simply return what we got */
}

END_C

my @tokens = (
    qw (
        LPAREN      [\(]
        RPAREN      [\)]
        CONCAT      ::
        NIL         nil
        IDENT       [A-Za-z_][A-Za-z0-9_]*
        CONST       (?:0(?:\.[0-9]+)?)|(?:[1-9][0-9]*(?:\.[0-9]+)?)|(?:\".+\")|(?:\'.+\')
    ),
    COMMA => q/,/
);

my $lexer = Parse::Lex->new(@tokens);
$lexer->skip('\s+');
my $parser = HOI::typeparser->new();

sub lexana {
    my $token = $lexer->next;
    if (not $lexer->eoi) {
        return ($token->name, $token->text);
    } else {
        return ('', undef);
    }
}

my %compiled_patterns;

sub pcompile {
    $lexer->from(shift);
    $parser->YYParse(yylex => \&lexana)
}

sub astmatch {
    my ($ast, $args) = @_;
    return (0, {}) if ($#{$ast} ne $#{$args});
    my %switches = (
        "const" =>
        sub {
            my ($sym, $val) = @_;
            if( (substr($sym, 0, 1) eq '\'') or (substr($sym, 0, 1) eq '"') ) {
                my $quote = substr($sym, 0, 1);
                return ($sym eq $quote.$val.$quote) ? (1, {}) : (0, {});
            } else {
                return ($sym == $val) ? (1, {}) : (0, {});
            }
        },
        "any" => 
        sub { 
            my ($sym, $val) = @_; 
            (1, ((substr($sym, 0, 1) ne '_') ? { $sym => $val } : {})) 
        },
        "list" => 
        sub { 
            my ($l, $val) = @_; 
            if (($#{$l} >= 0) and ($#{$val} >= 0)) {
                my ($s1, $r1) = astmatch([ $l->[0] ], [ $val->[0] ]);
                my ($s2, $r2) = astmatch([ $l->[1] ], [ [ @$val[1..$#{$val}] ] ]);
                return ($s1 * $s2, { %$r1, %$r2 });
            } elsif (($#{$l} < 0) and ($#{$val} < 0)) {
                return (1, {});
            } else {
                return (0, {});
            }
        },
        "adt" =>
        sub { 
            my ($adt, $val) = @_;
            return (0, {}) if ((not defined $val->{"type"}) or (not defined $val->{"val"}));
            my ($sym, $typelist) = ($adt->[0], $adt->[1]);
            return (0, {}) if ($adt->[0] ne $val->{"type"});
            return (0, {}) if ($#{$adt->[1]} != $#{$val->{"val"}});
            astmatch($adt->[1], $val->{"val"})
        }
    );
    my $ret = {};
    for (my $idx = 0; $idx <= $#{$ast}; $idx++) {
        my ($status, $result) = $switches{$ast->[$idx]->{"kind"}}->($ast->[$idx]->{"val"}, $args->[$idx]);
        if ($status) {
            $ret = { %$ret, %$result };
        } else {
            return (0, {})
        }
    }
    (1, $ret)
}

sub pmatch {
    my $patterns = \@_;
    sub {
        my $args = \@_;
        while (@$patterns) {
            my $pattern = shift @$patterns;
            my $handler = shift @$patterns;
            my $pattern_sig = (caller(1))[3].$pattern;
            $compiled_patterns{$pattern_sig} = pcompile($pattern) if (not defined $compiled_patterns{$pattern_sig});
            my $pattern_ast = $compiled_patterns{$pattern_sig};
            my ($status, $results) = astmatch($pattern_ast, $args);
            if ($status) {
                my ($package) = caller(1);
                local $AttrPrefix = $package.'::';
                my $attr_prefix = $package.'::';
                attr $results;
                return $handler->(%$results);
            }
        }
        0
    }
}

1;
__END__

=head1 NAME

HOI::Match - Higher-Order Imperative "Re"features in Perl

=head1 SYNOPSIS

  use HOI::Match;

  sub point_extract {
      HOI::Match::pmatch(
          "point (x _) :: r" => sub { my %args = @_; $args{x} + point_extract($args{r}) },
          "nil" => sub { 0 }
      )->(@_)
  }

  point_extract(
      [ 
          {"type" => "point", "val" => [ 1, 2 ]},
          {"type" => "point", "val" => [ 2, 4 ]},
          {"type" => "point", "val" => [ 3, 6 ]},
      ]
  ) # we will get 6


=head1 DESCRIPTION

HOI::Match offers Erlang-like pattern matching in function parameters. 
Currently only wildcard symbols, lists and algebraic-data-type like hashrefs
are supported.

A wildcard symbol ([A-Za-z_][A-Za-z0-9_]*) matches exactly one argument.
A list is represented as an array reference. 
An algebraic-data-typed object is represented as an hashref with two keys,
namely "type", which gives its typename, and "val", which is an array reference 
containing zero or more wildcard symbols, lists, or algebraic-data-typed objects.
Multiple constructors for a given algebraic data type named A are allowed.

The BNF used to define the pattern grammar is given below:


Types: Type 
     | Type COMMA Types 


Type: CONST
    | IDENT 
    | Type CONCAT Type 
    | NIL 
    | IDENT LPAREN Typelist RPAREN 


Typelist: <eps>
        | Type Typelist 


where

CONST = (?:0(?:\.[0-9]+)?)|(?:[1-9][0-9]*(?:\.[0-9]+)?)|(?:\".+\")|(?:\'.+\')

IDENT = [A-Za-z_][A-Za-z0-9_]*

CONCAT = ::

NIL = nil

LPAREN = (

RPAREN = )

COMMA = ,

are tokens.

=head2 pmatch

The function pmatch takes an hash-formed array, which contains pattern-
subroutine pairs, where patterns are strings, sequently.

The patterns will be matched sequently. That is,

    "x, y"
    "point (_ x), y"

on arguments 
    ( { "type" => "point", "val" => [ 1, 2 ] }, 3 ) 
will be successfully matched with pattern
    "x, y" 
instead of 
    "point (_ x), y".

On a successful match, the values corresponding to identifiers in the pattern
will be passed to the subroutine in a hash. You can access them as named arguments with

    my %args = @_;

Identifiers that begin with an underscore ('_') will be ignored. They will not
be passed to the subroutine.

Version 0.07 offers aliases for identifiers in the pattern under the support of Alias.
See the test files for details.

=head1 AUTHOR

withering <withering@cpan.org>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2014 by withering

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.18.2 or,
at your option, any later version of Perl 5 you may have available.


=cut

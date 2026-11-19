from argparse import ArgumentParser
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
PIN = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
IMPORT = re.compile(r'^(?:(?:public|private|meta) )*import (?:all )?([\w.]+)$', re.M)
ROOT = 'ErdosProblems.Erdos587.HooleyDyadicModel'

parser = ArgumentParser(description='Prepare the pinned Erdős 587 subset-sum proof for Lean 4.34.1.')
parser.add_argument('--checkout', type=Path, default=HERE / 'plby')
parser.add_argument('--output', type=Path, default=HERE / 'replay-src')
parser.add_argument('--order', type=Path, default=HERE / 'replay-order.txt')
args = parser.parse_args()

checkout = args.checkout.resolve()
git = ['git', '-C', str(checkout)]
actual_pin = subprocess.check_output([*git, 'rev-parse', 'HEAD'], text=True).strip()
if actual_pin != PIN:
    raise SystemExit(f'Expected upstream commit {PIN}, found {actual_pin}')
if subprocess.run([*git, 'diff', '--quiet', 'HEAD', '--', 'src/latest']).returncode:
    raise SystemExit(f'Upstream files under {checkout / "src/latest"} differ from {PIN}')

UPSTREAM = checkout / 'src/latest'
OUTPUT = args.output.resolve()

TACTICS = [
    'Lean.Elab.Tactic.Omega',
    'Mathlib.Tactic.Abel',
    'Mathlib.Tactic.FieldSimp',
    'Mathlib.Tactic.FinCases',
    'Mathlib.Tactic.GCongr',
    'Mathlib.Tactic.Linarith',
    'Mathlib.Tactic.LinearCombination',
    'Mathlib.Tactic.NormNum',
    'Mathlib.Tactic.Positivity',
    'Mathlib.Tactic.Push',
    'Mathlib.Tactic.Ring',
]

FINITE = [
    'Mathlib.Algebra.Group.Pointwise.Finset.Basic',
    'Mathlib.Algebra.Group.Pointwise.Finset.Scalar',
    'Mathlib.Algebra.Order.BigOperators.Ring.Finset',
    'Mathlib.Combinatorics.Additive.SubsetSum',
    'Mathlib.Data.Fintype.Pi',
    'Mathlib.Data.Int.Interval',
    'Mathlib.Data.Nat.Log',
    'Mathlib.Order.Interval.Finset.Nat',
]

COMMON = TACTICS + FINITE

ADDITIVE = [
    'Mathlib.Combinatorics.Additive.PluenneckeRuzsa',
    'Mathlib.Combinatorics.Additive.RuzsaCovering',
    'Mathlib.Analysis.SpecialFunctions.Pow.Real',
]

FOURIER = ['ReplayCircleChar']

NARROW_IMPORTS = {
    'FiniteFourier': FOURIER + [
        'Mathlib.Algebra.Order.BigOperators.Ring.Finset',
        'Mathlib.Analysis.RCLike.Basic',
        'Mathlib.Tactic.Linarith',
        'Mathlib.Tactic.Ring',
    ],
    'FiniteBogolyubov': [
        'Mathlib.Tactic.LinearCombination',
        'Mathlib.Tactic.NormNum',
        'Mathlib.Tactic.Positivity',
        'Mathlib.Tactic.GCongr',
    ],
    'AdelicMinkowski': [
        'Mathlib.Algebra.Order.BigOperators.Ring.Finset',
        'Mathlib.Analysis.Normed.Module.Basic',
        'Mathlib.Data.Fintype.Fin',
        'Mathlib.LinearAlgebra.LinearIndependent.Defs',
    ],
}

MODULE_IMPORTS = {
    'Erdos13Additive': ADDITIVE + [
        'Mathlib.Algebra.EuclideanDomain.Int',
        'Mathlib.Combinatorics.Additive.CauchyDavenport',
        'Mathlib.RingTheory.PrincipalIdealDomain',
    ],
    'FreimanModel': ADDITIVE + [
        'Mathlib.Algebra.Field.ZMod',
        'Mathlib.Combinatorics.Additive.FreimanHom',
        'Mathlib.Combinatorics.Pigeonhole',
    ],
    'Erdos587Core': [
        'Mathlib.Algebra.Field.ZMod',
        'Mathlib.Algebra.Module.ZMod',
        'Mathlib.Data.Nat.Prime.Basic',
    ],
    'Primitive': [
        'Mathlib.Algebra.EuclideanDomain.Int',
        'Mathlib.Algebra.GCDMonoid.FinsetLemmas',
        'Mathlib.Data.Int.GCD',
        'Mathlib.Data.Real.Basic',
    ],
    'GAPDefinitions': ['Mathlib.Data.Fintype.BigOperators'],
    'NVDevelopment': ADDITIVE + [
        'Mathlib.Data.Int.GCD',
        'Mathlib.Data.Nat.Choose.Cast',
    ],
    'DyadicScaleBudgets': ['Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics'],
}

NV_DEPENDENCY_SLICE = {
    'PolynomialDenseRows': 2,
    'GAPTrimVolumes': 7,
    'GAPCoordinates': 5,
    'HooleyLatticeRounding': 8,
    'HooleyConvexQuotient': 10,
    'HooleyInnerBox': 10,
    'GreedyDenseFiber': 13,
}

EXPLICIT_IMPORTS = {
    'CosetPacking': ['Mathlib.Algebra.Group.Subgroup.Basic'],
    'LatticeBoxPacking': ['Mathlib.Data.Fintype.BigOperators'],
    'LatticeIndexBound': [
        'Mathlib.GroupTheory.Index',
        'Mathlib.Algebra.BigOperators.Pi',
        'Mathlib.Algebra.Group.Subgroup.Finite',
    ],
    'GAPContraction': ['ErdosProblems.Erdos587.NVDevelopmentReplay13'],
    'HooleyCubeFiber': ['Mathlib.Analysis.Convex.KreinMilman'],
    'PolynomialDenseProper': ['ErdosProblems.Erdos587.NVDevelopmentReplay06'],
    'GreedyGrowthBounds': ['Mathlib.Basic.Real.Basic'],
}

PRIVATE_IMPORTS = {
    'GreedyDenseFiber': ['ErdosProblems.Erdos587.FreimanModel'],
    'HooleyLatticeCoordinates': [
        'Mathlib.GroupTheory.IndexNSmul',
        'Mathlib.LinearAlgebra.Dimension.Constructions',
        'Mathlib.LinearAlgebra.FreeModule.PID',
    ],
}

REPLACE_NV_IMPORT = {
    'FiniteQuotientCoverage': [
        'ErdosProblems.Erdos587.Erdos587Core',
        'Mathlib.GroupTheory.QuotientGroup.Basic',
    ],
    'HooleyBoxMass': [
        'Mathlib.Data.Fintype.BigOperators',
        'Mathlib.Algebra.Group.Action.Defs',
        'Mathlib.Data.Int.Interval',
        'Mathlib.Algebra.Order.BigOperators.Ring.Finset',
        'Lean.Elab.Tactic.Omega',
        'Mathlib.Tactic.Linarith',
        'Mathlib.Tactic.NormNum',
        'Mathlib.Tactic.Positivity',
        'Mathlib.Tactic.Ring',
    ],
}


def slim_nv(source: str) -> str:
    header = source[:source.index('import Mathlib')]
    body = source[source.index('namespace Erdos587\n'):source.index('/-! ## First analytic estimate')]
    structural = source[source.index('/-- The exact extremal quantity'):]
    structural = structural[:structural.index('/-- The pivot set at a stopped Nguyen--Vu generation')]
    structural = structural.replace('  · rw [Measure.volume_eq_prod]\n', '')
    dependencies = [
        'Mathlib',
        'ErdosProblems.Erdos13.Erdos13Additive',
        'ErdosProblems.Erdos587.NVStopping',
        'ErdosProblems.Erdos587.Erdos587Core',
    ]
    return (header + ''.join(f'import {name}\n' for name in dependencies)
            + '\nopen Filter\nopen scoped Pointwise\n\n'
            + body + structural + '\nend Erdos587\n')


def split_gap(source: str, only_link: bool) -> str:
    start = source.index('/-- The common integer-GAP presentation')
    end = source.index('/-- Coefficient vectors in the defining box', start)
    start_lemmas = source.index('@[simp] lemma rank_ofInteger', end)
    end_lemmas = source.index('lemma mem_carrier_iff', start_lemmas)
    if only_link:
        return ('import ErdosProblems.Erdos587.GAPDefinitions\n'
                'import ErdosProblems.Erdos587.CyclicGapLift\n\n'
                'namespace Erdos587.GeneralizedAP\n\n' + source[start:end]
                + source[start_lemmas:end_lemmas] + 'end Erdos587.GeneralizedAP\n')
    return (source[:start] + source[end:start_lemmas] + source[end_lemmas:]).replace(
        'import ErdosProblems.Erdos587.CyclicGapLift', 'import Mathlib')


def slim_adelic(source: str) -> str:
    header = source[:source.index('import Mathlib')] + 'import Mathlib\n'
    box = source[source.index('/-- A closed coordinate box centered at the origin.'):]
    box = box[:box.index('theorem realBox_volume')]
    certificate = source[source.index('/-- A concrete upper certificate'):]
    certificate = certificate[:certificate.index('/-- The standard coordinate points')]
    return (header + '\nnamespace Erdos407.AdelicMinkowski\n\nopen scoped BigOperators\n\n'
            + box + certificate + 'end Erdos407.AdelicMinkowski\n')


def slim_primitive(source: str) -> str:
    prefix = source[:source.index('/-- Coordinatewise coercion')]
    primitive = source[source.index('/-- A finite integral vector is primitive'):]
    primitive = primitive[:primitive.index('private def rowMatrix')]
    gcd = source[source.index('/-- The (nonnegative) gcd'):]
    gcd = gcd[:gcd.index('/-- The primitive integral normalization')]
    return (prefix.replace(' LinearAlgebra.Projectivization', '') + primitive + gcd
            + 'end Erdos407.Primitive\n')


def slim_minkowski(source: str) -> str:
    source = source.replace('import Mathlib.Algebra.Module.ZLattice.Covolume',
                            'import Mathlib.LinearAlgebra.Matrix.Block\nimport ReplayLattice')
    source = source.replace('ZSpan.setFinite_inter b Metric.isBounded_closedBall',
                            'Erdos407.ReplayLattice.finite_span_inter_bounded b Metric.isBounded_closedBall')
    start = source.index('  let L : Submodule ℤ', source.index('theorem abs_det_zspan_basis_eq'))
    end = source.index('/-- Cast an integral coordinate vector', start)
    return (source[:start] + '  exact Erdos407.ReplayLattice.abs_det_zspan_basis_eq_of_change b B\n\n'
            + source[end:])


def split_bohr(source: str, geometry: bool) -> str:
    membership = source.index('theorem bohrCyclicProgression_carrier_subset')
    size = source.index('/-! ## Quantitative size of the progression')
    assembly = source.index('theorem exists_proper_cyclicProgression_in_fourfoldDifference')
    suffix = '\nend\n\nend Erdos587\n'
    if geometry:
        first = source[:membership].replace('import ErdosProblems.Erdos587.BohrPhase',
            'import Mathlib.Data.ZMod.Basic\nimport Mathlib.Tactic.FinCases')
        return first + source[size:assembly] + suffix
    return ('import ErdosProblems.Erdos587.BohrGeometry\n'
            'import ErdosProblems.Erdos587.Bohr\n\n'
            'import ErdosProblems.Erdos587.BohrCharacterBound\n\n'
            'open scoped BigOperators Matrix Pointwise\n\nnamespace Erdos587\n\n'
            'noncomputable section\n\n' + source[membership:size] + source[assembly:])


def split_bohr_character(source: str, only_bound: bool) -> str:
    marker = source.index('/-- A residue represented by an integer of absolute value')
    if not only_bound:
        return source[:marker] + 'end Erdos587\n'
    imports = ['ReplayCircleChar', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds',
               'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.NormNum', 'Mathlib.Tactic.Ring']
    return (''.join(f'import {dep}\n' for dep in imports) + '\nnamespace Erdos587\n\n'
            + source[marker:])


def active_namespaces(source: str) -> list[str]:
    names: list[str] = []
    declaration = re.compile(r'^(namespace|end) ([\w.]+)$', re.M)
    for action, name in declaration.findall(source):
        if action == 'namespace':
            names.append(name)
        else:
            if not names or names.pop() != name:
                raise ValueError(f'Mismatched namespace ending `{name}`')
    return names


def split_nv(name: str, source: str, seen: set[str], ordered: list[str]) -> str:
    # These markers start complete declarations or doc sections, never tactic blocks.
    markers = [
        '/-! ### Dense fibers of a coefficient box',
        '/-- A small-sum pair appearing inside an iterated sumset',
        '/-- Any iterated sum of distinct generation values',
        '/-! ## Collision counting for non-proper progressions',
        '/-- Ordinary properness controls the linear evaluation map',
        '/-- The rank-zero GAP supported on one integer',
        '/-! ### Convex progressions for the proper-embedding lemma',
        '/-- Existence of a shortest nonzero lattice vector',
        '/-- Integral coordinates with respect to an arbitrary lattice basis',
        '/-- Recursive adapted basis with both a dilation bound',
        '/-- Failure of `t`-properness gives a nonzero relation',
        '/-- Number of Ruzsa translates used to cover a small-doubling set',
    ]
    boundaries = [0, *(source.index(marker) for marker in markers), len(source)]
    if sorted(set(boundaries)) != boundaries:
        raise ValueError('Expected each structural section once and in source order')
    freiman_begin = '/-! ## The quantitative Freiman step in Nguyen--Vu -/'
    freiman_end = '/-- A GAP presentation containing the difference set `P - P`. -/'
    freiman_start, freiman_stop = source.index(freiman_begin), source.index(freiman_end)
    resume = source.rindex('namespace GeneralizedAP', freiman_start, freiman_stop)
    freiman = source[freiman_start:resume].replace('def freimanModelDensity',
                '@[expose] def freimanModelDensity').replace('def freimanCyclicRank',
                '@[expose] def freimanCyclicRank').replace('noncomputable def freimanCyclicDenominator',
                'private noncomputable def freimanCyclicDenominator').replace('lemma freimanCyclicDenominator_pos',
                'private lemma freimanCyclicDenominator_pos')
    freiman_name = 'ErdosProblems.Erdos587.ReplayFreimanCore'
    freiman_link = 'ErdosProblems.Erdos587.ReplayGAPLink'
    gap = 'ErdosProblems.Erdos587.GAPDefinitions'
    previous = ''
    extra = {
        2: ['Mathlib.Data.Pi.Interval'],
        5: [gap],
        6: ['Mathlib.Combinatorics.Pigeonhole'],
        8: [
            'Mathlib.Analysis.Convex.Gauge',
            'Mathlib.Analysis.Convex.Combination',
            'Mathlib.Analysis.Normed.Module.FiniteDimension',
            'Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar',
            'Mathlib.Tactic.FunProp',
        ],
        13: [freiman_name],
    }
    for index, (start, end) in enumerate(zip(boundaries, boundaries[1:], strict=False), 1):
        part = f'{name}Replay{index:02}'
        prefix = ''
        if start:
            imports = extra.get(index, [])
            for dep in imports:
                prepare(dep, seen, ordered)
            prefix = f'module\n\npublic import {previous}\n'
            prefix += ''.join(f'public import {dep}\n' for dep in imports)
            if index == 7:
                prefix += ('import Mathlib.LinearAlgebra.FreeModule.PID\n'
                           'import Mathlib.LinearAlgebra.Dimension.Constructions\n')
            prefix += '\n@[expose] public section\n\n'
            prefix += ('open Filter MeasureTheory\n' if index >= 8 else 'open Filter\n')
            prefix += 'open scoped Pointwise\n\n'
            prefix += ''.join(f'namespace {ns}\n' for ns in active_namespaces(source[:start]))
        suffix = ''.join(f'end {ns}\n' for ns in reversed(active_namespaces(source[:end])))
        content = source[start:end]
        if start < freiman_start < freiman_stop < end:
            close = source.rindex('end GeneralizedAP', start, freiman_start)
            content = source[start:close] + source[freiman_stop:end]
        write_source(part, prefix + content + suffix)
        ordered.append(part)
        if index == 5:
            prepare(freiman_link, seen, ordered)
            freiman_source = (f'module\n\npublic import {name}Replay01\npublic import {gap}\n'
                f'import {freiman_link}\n\npublic section\n\nopen scoped BigOperators Pointwise\n'
                '\nnamespace Erdos587\n\n' + freiman + 'end Erdos587\n')
            write_source(freiman_name, freiman_source)
            ordered.append(freiman_name)
        previous = part
    return f'module\n\npublic import {previous}\n'


def write_source(name: str, source: str) -> None:
    output = OUTPUT / Path(*name.split('.')).with_suffix('.lean')
    output.parent.mkdir(parents=True, exist_ok=True)
    if not output.is_file() or output.read_text() != source:
        output.write_text(source)


def prepare(name: str, seen: set[str], ordered: list[str]) -> None:
    if name in seen:
        return
    seen.add(name)
    relative = Path(*name.split('.')).with_suffix('.lean')
    if name in ('ReplayCircleChar', 'ReplayLattice'):
        original = HERE / relative
    elif name == 'ErdosProblems.Erdos587.BohrGeometry':
        original = UPSTREAM / relative.with_name('BohrProgression.lean')
    elif name == 'ErdosProblems.Erdos587.BohrCharacterBound':
        original = UPSTREAM / relative.with_name('Bohr.lean')
    elif name == 'ErdosProblems.Erdos587.ReplayGAPLink':
        original = UPSTREAM / relative.with_name('GAPDefinitions.lean')
    else:
        original = UPSTREAM / relative
    if not original.is_file():
        return
    source = original.read_text()
    short = name.split('.')[-1]
    if short == 'NVDevelopment':
        source = slim_nv(source)
    if short == 'AdelicMinkowski':
        source = slim_adelic(source)
    if short == 'Primitive':
        source = slim_primitive(source)
    if short in ('GAPDefinitions', 'ReplayGAPLink'):
        source = split_gap(source, only_link=short == 'ReplayGAPLink')
    if short == 'MinkowskiSecondBox':
        source = slim_minkowski(source)
    if short in ('BohrGeometry', 'BohrProgression'):
        source = split_bohr(source, geometry=short == 'BohrGeometry')
    if short in ('Bohr', 'BohrCharacterBound'):
        source = split_bohr_character(source, only_bound=short == 'BohrCharacterBound')
    if short == 'BohrGeometry':
        source = source.replace('apply Finset.prod_le_prod\n', 'apply Finset.prod_le_prod₀\n')
    if name != 'ReplayCircleChar':
        source = source.replace('ZMod.stdAddChar', 'ZMod.replayStdAddChar')
        source = source.replace('ZMod.isPrimitive_stdAddChar', 'ZMod.isPrimitive_replayStdAddChar')
    if short == 'BohrPhase':
        source = 'import Mathlib.Combinatorics.Pigeonhole\n' + source
    if short == 'MinkowskiSecondBoxBasis':
        source = 'import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas\n' + source
        source = source.replace('(by simp)', '(by simp only [Fintype.card_fin, Module.finrank_fin_fun])')
        source = source.replace('simp [projectedTailBasis]',
            'simp only [projectedTailBasis, coe_basisOfLinearIndependentOfCardEqFinrank\']')
    if short == 'MinkowskiSecondBoxGlue':
        to_real = 'Erdos407.ReplayLattice.realBasisFromZSpan'
        source = source.replace('Bz.ofZLatticeBasis ℝ L', f'{to_real} b Bz')
        source = source.replace('Basis.ofZLatticeBasis_apply ℝ L Bz 0', f'{to_real}_apply b Bz 0')
        source = source.replace('Bz.ofZLatticeBasis_span ℝ L', f'{to_real}_span b Bz')
    if short == 'MinkowskiDiagonalNormalization':
        source = 'import Mathlib.LinearAlgebra.Matrix.Determinant.Basic\n' + source
    if short in EXPLICIT_IMPORTS:
        source = ''.join(f'import {dep}\n' for dep in EXPLICIT_IMPORTS[short]) + source
    if short == 'GreedySubsetSums':
        marker = '/-- A fixed repeated-sum threshold gives multiplicative growth at every step. -/'
        empty_subset_sum = ('theorem empty_subsetSum_eq_singleton : (∅ : Finset G).subsetSum = {0} := by\n'
                            '  ext x\n'
                            '  simp [Finset.mem_subsetSum_iff, eq_comm]\n\n')
        source = source.replace(marker, empty_subset_sum + marker)
    if short in ('GreedySubsetSums', 'GreedyDensity'):
        source = source.replace('simp [Finset.subsetSum]', 'simp [empty_subsetSum_eq_singleton]')
    source = re.sub(r'^#print axioms [^\n]*\n?', '', source, flags=re.M)
    source = re.sub(r'Finset\.prod_le_prod \(fun \w+ \w+ => Nat\.zero_le _\)(?=\s)',
                    'Finset.prod_le_prod', source)
    imports = IMPORT.findall(source)
    if 'Mathlib' in imports:
        selected = NARROW_IMPORTS.get(short, COMMON + MODULE_IMPORTS.get(short, []))
        explicit = ''.join(f'import {dep}\n' for dep in selected)
        source = re.sub(r'^import Mathlib$', explicit.rstrip(), source, count=1, flags=re.M)
        imports = [dep for dep in imports if dep != 'Mathlib'] + selected
    if not re.search(r'^module(?:[ \t]+--[^\n]*)?[ \t]*$', source, re.M):
        source = re.sub(r'^import ', 'public import ', source, flags=re.M)
        entries = list(IMPORT.finditer(source))
        if entries:
            start, end = entries[0].start(), entries[-1].end()
            source = source[:start] + 'module\n\n' + source[start:end] + '\n\n@[expose] public section\n' + source[end:]
    if short == 'BohrCharacterBound':
        source = source.replace('public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds',
                                'import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds')
    if short == 'BohrProgression':
        source = source.replace('public import ErdosProblems.Erdos587.BohrCharacterBound',
                                'import ErdosProblems.Erdos587.BohrCharacterBound')
    if short in PRIVATE_IMPORTS:
        source = source.replace('@[expose] public section',
            ''.join(f'import {dep}\n' for dep in PRIVATE_IMPORTS[short]) + '\n'
            '@[expose] public section')
    if short == 'HooleyLatticeCoordinates':
        source = source.replace('noncomputable def deltaFiniteIndexBasis',
                                '@[no_expose] noncomputable def deltaFiniteIndexBasis')
    for dep in imports:
        prepare(dep, seen, ordered)
    if short in NV_DEPENDENCY_SLICE:
        dependency = 'ErdosProblems.Erdos587.NVDevelopment'
        slice_number = NV_DEPENDENCY_SLICE[short]
        source = source.replace(f'import {dependency}\n',
                                f'import {dependency}Replay{slice_number:02}\n')
    if short in REPLACE_NV_IMPORT:
        source = source.replace('public import ErdosProblems.Erdos587.NVDevelopment\n',
            ''.join(f'public import {dep}\n' for dep in REPLACE_NV_IMPORT[short]))
    if short == 'NVDevelopment':
        source = split_nv(name, source, seen, ordered)
    write_source(name, source)
    ordered.append(name)


order: list[str] = []
prepare(ROOT, set(), order)
args.order.parent.mkdir(parents=True, exist_ok=True)
args.order.write_text('\n'.join(order) + '\n')
print(f'{len(order)} modules written to {OUTPUT}')

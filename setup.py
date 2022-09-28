from typing import NamedTuple, Optional, Callable, Union, Tuple, List, Dict, Set, Any
from distutils.command.build import build as BuildOriginal  # TODO: remove before 3.12(?)
from multiprocessing import cpu_count
from contextlib import contextmanager
from zipfile import ZipFile
from hashlib import sha256
from pathlib import Path
from enum import Enum
from glob import glob
import subprocess
import platform
import tempfile
import tarfile
import string
import shutil
import sys
import os
import re

from setuptools.command.sdist import sdist as SDistOriginal
from setuptools import setup, Command
from tqdm import tqdm
import requests

# Shared libraries
import z3

######################################################################
#                              Globals                               #
######################################################################

# Paths
claripy = Path(__file__).absolute().parent
native: Path = claripy / "native"

with open(claripy / "VERSION") as f:
    version: str = f.read().strip()

# Clari library names; these should be in MANIFEST.in
clari: str = "clari"

######################################################################
#                              Helpers                               #
######################################################################


class JDict(dict):
    """
    A key-read-only dict that allows . semantics
    """

    __getattr__ = dict.get
    __setattr__ = None
    __delattr__ = None


@contextmanager
def chdir(new: Path) -> None:
    """
    Current working directory context manager
    """
    old: str = os.getcwd()
    new = new.absolute()
    try:
        print(f"cd {new}")
        os.chdir(new)
        yield
    finally:
        print(f"cd {old}")
        os.chdir(old)


def find_exe(name: str, fail_ok: bool = False) -> Path:
    """
    Akin to bash's which function
    """
    exe: str = shutil.which(name, mode=os.X_OK)
    if exe is None and not fail_ok:
        raise RuntimeError(f"Cannot find {name}")
    return Path(exe).absolute()


def cname(x: type) -> str:
    """
    Return the class name of x
    """
    return x.__class__.__name__


class BuiltLib:
    """
    A shared or static library
    """
    install_dir: Path = claripy / "claripy" / "native" / "lib"

    def __init__(self, name: str, build_dir: Path, *, permit_shared: bool, permit_static: bool):
        self.name: str = name
        self._lic: Path = self.install_dir / f"LICENSE.{name}".replace(" ", "_")
        self.build_dir: Path = build_dir
        # Determine extensions
        self._permit_shared: bool = permit_shared
        self._permit_static: bool = permit_static
        self._licensed: bool = False

    def init_license(self, installer: Callable, cleaner: Callable) -> None:
        """
        Install license handling functions
        """
        self._lic_installer: Callable = installer
        self._lic_cleaner: Callable = cleaner

    def _find_ext(self, where: Path, ext: str) -> Path:
        exact = (where / f"{self.name}.{ext}").resolve()
        if exact.exists():
            return exact
        files: List[str] = glob(f"{where / self.name}.*")
        # Check ext after glob b/c .'s can overlap
        files: List[str] = [i for i in files if i.endswith(f".{ext}")]
        if len(files) == 1:
            return Path(files[0]).absolute()
        if len(files) > 1:
            print(f"Found: {files}")
            raise RuntimeError(f"Multiple {self.name} libraries in {where} with the same extension: {ext}: {files}")

    def _find(self, where: Path) -> Optional[Path]:
        """
        Tries to find a library within the directory where
        Will prefer the native file extension type but may permit others
        Static libraries have the lowest preference
        """
        exts: List[str] = []
        if self._permit_shared:
            ops: str = platform.system()
            if ops == "Darwin":
                exts.extend(["dylib", "so"])
            elif ops == "Windows":
                exts.extend(["dll", "so"])
            else:
                exts.extend(["so", "dll", "dylib"])
        if self._permit_static:
            exts.append("a")
        found: List[Path] = [self._find_ext(where, i) for i in exts]
        found: List[Path] = [i for i in found if i is not None]
        return found[0] if found else None

    def find_installed(self) -> Optional[Path]:
        """
        Look for the library in the installation directory
        """
        return self._find(self.install_dir)

    def find_built(self) -> Optional[Path]:
        """
        Look for the library in the build directory
        """
        return self._find(self.build_dir)

    def licensed(self, b: bool) -> None:
        self._licensed: bool = b

    def install(self) -> None:
        """
        Copies the library from build dir to install dir
        """
        assert self._licensed is not None, "Will not install without a license"
        p: Optional[Path] = self.find_built()
        assert p is not None, "Cannot install a non-built library"
        if not self.install_dir.exists():
            print(f"Creating install dir {self.install_dir}")
            self.install_dir.mkdir()
        shutil.copy2(p, self.install_dir)

    def _clean(self, x: Optional[Path]) -> None:
        if x:
            x.unlink()

    def clean_build(self) -> None:
        self._clean(self.find_built())

    def clean_install(self) -> None:
        self._clean(self.find_installed())


class Downloadable(NamedTuple):
    """
    A downloadable object
    """
    url: str
    sha: str
    ext: str


class SharedLib(BuiltLib):
    """
    A shared library
    """

    def __init__(self, name: str, build_dir: Path):
        super().__init__(name, build_dir, permit_shared=True, permit_static=False)


class StaticLib(BuiltLib):
    """
    A shared library
    """

    def __init__(self, name: str, build_dir: Path):
        super().__init__(name, build_dir, permit_shared=False, permit_static=True)


def run_cmd_no_fail(*args: Union[str, Path], **kwargs: Any) -> int:
    """
    A wrapper around subprocess.run that errors on subprocess failure
    Note: paths should be passes as pathlib.Path objects, not strs!
    Returns subprocess.run(args, **kwargs)
    """
    args: List[str] = list(args)
    print(f"Running command: {args}")
    rc: subprocess.CompletedProcess = subprocess.run(args, **kwargs)
    if rc.returncode != 0:
        if rc.stdout:
            print(rc.stdout)
        if rc.stderr:
            print(rc.stderr, file=sys.stderr)
        raise RuntimeError(f"{args[0].parent} failed with return code: {rc.returncode}")
    return rc


def extract(d: Path, f: Path, ext: str) -> None:
    """
    Extract f into d, the compression is assumed from the extension (ext)
    No leading period is allowed in ext
    """
    if ext.startswith("tar"):
        with tarfile.open(f) as z:
            z.extractall(d)
    elif ext == "zip":
        with ZipFile(f) as z:
            z.extractall(d)
    else:
        raise RuntimeError("Compression type not supported: " + ext)


def build_cmake_target(target: str, *args: Union[str, Path]) -> int:
    """
    Build the target with multiple jobs
    Extra args may be passed to the generator via args
    Run this from the same directory you would the generator
    Return the exit code of the run command
    """
    return run_cmd_no_fail(
        find_exe("cmake"), "--build", ".",
        f"-j{max(cpu_count() - 1, 1)}",
        "--target", target,
        "--", *args
    )


def download_checksum_extract(name: str, where: Path,
                              down: Downloadable) -> Tuple[Path, List[Path]]:
    """
    Download a file from url, checksum it, then extract it into a temp dir
    Return the temp dir and the files within it
    """
    print(f"Downloading and hash-verifying {name}...")
    hasher = sha256()
    prefix: str = re.sub(r"\s+", "_", name) + "-"
    fd, comp_f = tempfile.mkstemp(dir=where, prefix=prefix, suffix=f".{down.ext}")
    with os.fdopen(fd, "wb") as f:
        with requests.get(down.url, allow_redirects=True, stream=True) as r:
            r.raise_for_status()
            with tqdm(total=int(r.headers["Content-length"]), leave=False,
                      unit="B", unit_scale=True, unit_divisor=1024) as prog:
                chunk_size: int = 2**16
                for block in r.iter_content(chunk_size=chunk_size):
                    hasher.update(block)
                    f.write(block)
                    prog.update(chunk_size)
    if hasher.hexdigest() != down.sha:
        raise RuntimeError(f"Downloaded {name} hash failure!")
    # Extract
    raw = Path(tempfile.mkdtemp(dir=where, prefix=f"{prefix}dir-", suffix=".tmp"))
    print(f"Extracting {name} to: {raw}")
    extract(raw, comp_f, down.ext)
    os.remove(comp_f)
    return raw, [Path(i).absolute() for i in glob(f"{raw}/*")]


class CleanLevel(Enum):
    """
    Higher clean levels imply lower clean levels
    Values will be incremented by 1 between levels
    Non-whole values are allowed but may only be referenced in clean functions
    """
    INSTALL = 1
    LICENSE = 2
    BUILT_LIBS = 2.5
    BUILD = 3
    BUILD_DEPS = 3.5
    GET = 4


# 'Member functions' of CleanLevel
setattr(type(CleanLevel.GET), "implies", lambda self, o: self.value >= o.value)
setattr(type(CleanLevel.GET), "inc", lambda self: CleanLevel(self.value + 1))


def to_clean_lvl(name: str) -> int:
    """
    Get the clean level named name
    """
    name: str = name.upper()
    try:
        return getattr(CleanLevel, name)
    except AttributeError:
        valid: str = "Valid clean levels: " + ", ".join([i.name for i in CleanLevel])
        raise Exception(f"Invalid clean level: {name}. {valid}")


######################################################################
#                         Dependency Classes                         #
######################################################################


class Library:
    """
    Native dependencies should derive from this
    Subclasses may want to override _get, _build, _install, and _clean
    """

    def __init__(self, get_chk: Dict[str, Path], build_chk: Dict[str, Path],
                 install_chk: Dict[str, Path], *dependencies: "Library"):
        """
        get_chk, build_chk, and install_chk are dicts to given to _body
        When call .get(), self._done(*i) will be called for i in get_chk
        If all return true, the get stage will be skipped
        Likewise this is true for build_chk/install_chk stages build/install
        Note: If any values in the chk dicts are BuiltLibs, they will be swapped
        for the the .find_built / .find_installed functions as needed
        Subclasses must override _license
        Will only call _get, _build, _license, and _install once
        """
        self._done_set: Set[Path] = set()
        self._dependencies: List[Library] = dependencies
        assert self._dep_check(type(self)), f"Cyclical dependency found on: {type(self)}"
        # Done check lists
        self._get_chk: Dict[str, Path] = dict(get_chk)
        self._build_chk: Dict[str, Path] = self._fix_chk(build_chk, "find_built")
        self._install_chk: Dict[str, Path] = self._fix_chk(install_chk, "find_installed")

    @staticmethod
    def _fix_chk(d: Dict[str, str], name: str) -> Dict[str, str]:
        """
        Return a new dict which replaces BuiltLib values with their name functions
        """
        return {i: getattr(k, name) if isinstance(k, BuiltLib) else k
                for i, k in d.items()}

    def _dep_check(self, t: type) -> bool:
        """
        Return true iff no self does not depend on anything of type t
        """
        return all(not isinstance(i, t) and i._dep_check(t)
                   for i in self._dependencies)

    def _done(self, name: str, path: Union[Path, Callable[[], Path]]) -> bool:
        """
        If path is a function, path = path()
        If path exists, note it will be reused and return True
        This will only warn once per path!
        path may be None
        """
        if callable(path):
            path: Path = path()
        ret: bool = False if path is None else path.exists()
        if path in self._done_set:
            assert ret, f"{path} used to exist but now does not"
        elif ret:
            print(f"Reusing existing {name}: {path}")
            self._done_set.add(path)
        return ret

    def _call_format(self, x: type, n: str) -> str:
        return f"{cname(x)}.{n}()"

    def _call(self, origin: str, obj: Any, fn: Callable[[Set[str]], None],
              called: Set[str]) -> None:
        what: str = self._call_format(obj, fn)
        if what not in called:
            called.add(what)
            me: str = self._call_format(self, origin)
            print(f"{me} invoking {what}")
            getattr(obj, fn)(called)
            print(f"Resuming {me}")

    def _body(self, lvl: CleanLevel, chk: Dict[str, Path], called: Set[str]) -> None:
        """
        A helper function used to automate the logic of invoking dependencies and body
        Note: for lvl = license, license files are force cleaned!
        @param lvl: The clean level to be used for this
        @param chk: A dict where each entry contains the arguments to give to _done
        @param called: The set of already called methods
        If all calls to self._done pass, skip this stage
        If chk is empty, this stage will not be skipped
        """
        # Skip if everything is done
        if len(chk) and all([self._done(*i) for i in chk.items()]):
            return
        # Call dependent levels
        next: Optional[str] = None
        lvl_name: str = lvl.name.lower()
        try:
            next = lvl.inc().name.lower()
        except ValueError:
            pass
        if next is not None:
            self._call(lvl_name, self, next, called)
        # Call current level dependencies
        for obj in self._dependencies:
            self._call(lvl_name, obj, lvl_name, called)
        getattr(self, "_" + lvl_name)()
        called.add(self._call_format(self, lvl_name))

    def get(self, called: Optional[Set[str]] = None) -> None:
        """
        Acquire source files for this class and dependencies
        May reuse existing files
        """
        called: Set[str] = set() if called is None else called
        self._body(CleanLevel.GET, self._get_chk, called)

    def build(self, called: Optional[Set[str]] = None) -> None:
        """
        Build libraries for this class and dependencies
        """
        called: Set[str] = set() if called is None else called
        self._body(CleanLevel.BUILD, self._build_chk, called)

    def license(self, called: Optional[Set[str]] = None) -> None:
        """
        Install library licenses; will call ._license if it has not been called
        May reuse existing files
        """
        called: Set[str] = set() if called is None else called
        self._body(CleanLevel.LICENSE, {}, called)

    def install(self, called: Optional[Set[str]] = None) -> None:
        """
        Install libraries and source files for this class and dependencies
        May reuse existing files
        """
        called: Set[str] = set() if called is None else called
        self._body(CleanLevel.INSTALL, self._install_chk, called)

    def clean(self, level: CleanLevel) -> None:
        """
        Cleans up after the library
        """
        p = lambda x: f"{cname(x)}.clean({level.name})"
        for i in self._dependencies:
            print(f"{p(self)} invoking {p(i)}")
            i.clean(level)
        self._clean(level)

    def _get(self) -> None:
        """
        A function subclasses should override to get source files
        No need to handle dependencies in this
        """
        pass

    def _build(self) -> None:
        """
        A function subclasses should override to build libraries
        No need to handle dependencies in this
        """
        pass

    def _license(self) -> None:
        """
        A function subclasses must override to install licenses
        No need to handle dependencies in this
        """
        raise RuntimeError("No licenses installed")

    def _install(self) -> None:
        """
        A function subclasses should override to install libaries
        No need to handle dependencies in this
        """
        pass

    def _clean(self, level) -> None:
        """
        A function subclasses should override to clean up
        No need to handle dependencies in this
        """
        pass


class GMP(Library):
    """
    A class to manage GMP
    """

    _down = Downloadable(
        url="https://ftp.gnu.org/gnu/gmp/gmp-6.2.1.tar.xz",
        sha="fd4829912cddd12f84181c3451cc752be224643e87fac497b69edddadc49b4f2",
        ext="tar.gz")
    # Paths
    _root: Path = native / "gmp"
    _source: Path = _root / "src"
    _build_dir: Path = _root / "build"
    include_dir: Path = _root / "include"
    lib_dir: Path = _build_dir / ".libs"
    # We are ok with either static or shared, but we prefer shared
    _lib_default = BuiltLib("libgmp", lib_dir, permit_static=True, permit_shared=True)
    _lic_d: Path = BuiltLib.install_dir / "LICENSE.GMP"
    _lib: Path = _lib_default

    def __init__(self):
        get_chk: Dict[str, Path] = {"GMP source": self._source}
        build_chk: Dict[str, Path] = {
            "GMP license": self._source / "COPYINGv3",
            "GMP library": self._lib,
            "GMP include directory": self.include_dir,
        }
        install_chk: Dict[str, Path] = {"GMP lib": self._lib.find_installed}
        super().__init__(get_chk, build_chk, install_chk)

    def _get(self) -> None:
        self._root.mkdir(parents=True, exist_ok=True)
        d, gmp = download_checksum_extract("GMP source", self._root, self._down)
        print(f"Moving GMP source to: {self._source}")
        assert len(gmp) == 1, "gmp's tarball is weird"
        gmp[0].rename(self._source)
        d.rmdir()

    def _set_lib_type(self, config_log: Path) -> None:
        """
        Determine the built library type
        Run this during the build stage, after the build!
        """
        sh_lib_str: str = "Shared libraries:"
        with config_log.open("r") as f:
            lines: List[str] = [i for i in f.readlines() if sh_lib_str in i]
        assert len(lines) == 1, "./configure gave weird output"
        is_static: bool = lines[0].replace(sh_lib_str, "").strip() == "no"
        print(f"GMP lib type: {'static' if is_static else 'shared'}")
        lib_type: type = StaticLib if is_static else SharedLib
        self._lib = lib_type(self._lib.name, self._lib.build_dir)

    def _run(self, name: str, *args: str, _count: int = 0) -> Path:
        """
        A wrapper for run
        _count should only be used by this function
        """
        whitelist: str = string.ascii_lowercase + string.digits + "_-"
        base: str = "".join([i for i in name.lower().replace(" ", "_") if i in whitelist])
        base += f"{'' if _count == 0 else f'_{_count}'}.log"
        log_f: Path = self._build_dir / f"setup-py-{base}"
        if log_f.exists():
            return self._run(name, *args, _count=_count + 1)
        with log_f.open("w") as f:
            print(f"{name}...\n  - Output file: f{log_f}")
            sys.stdout.write("  - ")
            run_cmd_no_fail(*args, stdout=f, stderr=f)
        return log_f

    def _build(self) -> None:
        print(f"Copying source to build dir: {self._build_dir}")
        shutil.copytree(self._source, self._build_dir)  # Do not pollute source
        with chdir(self._build_dir):
            # GMP warnings:
            # 1. GMP's online docs are incomplete
            # 2. GMP's detection of ld's shared lib support is broken on at least macOS
            # TODO: host=none is slow
            # TODO: enable-shared=mpz ?
            # If GMP's build system refuses to use a shared library, fallback to static
            config_args = [
                "--with-pic",
                "--disable-static",
                "--enable-shared",
                "--host=none",
            ]
            self._set_lib_type(self._run("Configuring", "./configure", *config_args))
            # Building + Checking (GMP requires make)
            makej: Tuple[str] = (find_exe("make"), f"-j{max(cpu_count() - 1, 1)}")
            _ = self._run("Building GMP", *makej)
            _ = self._run("Checking GMP build", *makej, "check")
            # Include dir
            self.include_dir.mkdir()
            shutil.copy2(self._build_dir / "gmp.h", self.include_dir)

    def _license(self) -> None:
        if not self._lic_d.exists():
            print(f"Creating {self._lic_d}")
            self._lic_d.mkdir(parents=True)

        def cpy(src: str, dst: str):
            src: Path = self._build_dir / src
            dst: Path = self._lic_d / dst
            print(f"Copying {src} --> {dst}")
            shutil.copy2(src, dst)

        cpy("COPYINGv3", "GNU-GPLv3")
        cpy("AUTHORS", "AUTHORS")
        cpy("COPYING.LESSERv3", "GNU-LGPLv3")
        print("Generating README...")
        with (self._lic_d / "README").open("w") as f:
            msg = "The compiled GMP library is licensed under the GNU LGPLv3. The library was built from unmodified source code which can be found at: "
            f.write(f"{msg}{self._down.url}")

    def _install(self) -> None:
        self._lib.install()

    def _clean(self, level: CleanLevel) -> None:
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.LICENSE):
            shutil.rmtree(self._lic_d, ignore_errors=True)
        if level.implies(CleanLevel.BUILD_DEPS):
            shutil.rmtree(self._build_dir, ignore_errors=True)
            shutil.rmtree(self.include_dir, ignore_errors=True)
            self._lib.clean_build()
            self._lib = self._lib_default  # Reset lib type
        if level.implies(CleanLevel.GET):
            shutil.rmtree(self._root, ignore_errors=True)


class Boost(Library):
    """
    A class used to manage Boost
    """

    root: Path = native / "boost"
    _inc: Path = root / "boost"
    _lic: Path = root / "LICENSE"

    def __init__(self):
        # Boost depends on GMP
        super().__init__({"boost headers": self._inc, "boost license": self._lic}, {}, {}, GMP())

    @staticmethod
    def url_data() -> Downloadable:
        """
        Get the correct downloadable for the given OS
        """
        return {
            # Get this info from: https://www.boost.org/users/download/
            "posix": Downloadable(
                url="https://boostorg.jfrog.io/artifactory/main/release/1.78.0/source/boost_1_78_0.tar.gz",
                sha="94ced8b72956591c4775ae2207a9763d3600b30d9d7446562c552f0a14a63be7",
                ext="tar.gz",
            ),
            "nt": Downloadable(
                url="https://boostorg.jfrog.io/artifactory/main/release/1.78.0/source/boost_1_78_0.zip",
                sha="f22143b5528e081123c3c5ed437e92f648fe69748e95fa6e2bd41484e2986cc3",
                ext="zip",
            ),
        }[os.name]

    def _get(self) -> None:
        self._clean(CleanLevel.GET)  # Do not operate on a dirty boost dir
        self.root.mkdir()
        d, fs = download_checksum_extract("boost headers", self.root, self.url_data())
        print("Installing boost license...")
        if len(fs) != 1:
            raise RuntimeError("Boost should decompress into a single directory.")
        shutil.copy2(fs[0] / "LICENSE_1_0.txt", self._lic)
        print("Installing boost headers...")
        (fs[0] / "boost").rename(self.root / "boost")
        print("Cleaning temporary files...")
        shutil.rmtree(d)

    def _license(self):
        pass  # Nothing to install

    def _clean(self, level):
        if level.implies(CleanLevel.GET):
            if self.root.exists():
                shutil.rmtree(self.root)


class Z3(Library):
    """
    A class used to manage the z3 dependency
    Z3 has no dependencies; it should be pre-installed
    """

    _root = Path(z3.__file__).parent
    include_dir: Path = _root / "include"
    lib = SharedLib("libz3", _root / "lib")

    def __init__(self):
        super().__init__({}, {}, {"Z3 library": self.lib.find_installed})

    # _get is simply that _root has been resolved
    # Z3's pip has no license file so nothing for us to copy

    def _build(self) -> None:
        assert self.lib.find_built(), "Z3 is missing"

    def _license(self) -> None:
        pass  # Nothing to install


class Backward(Library):
    """
    A class used to manage the backward dependency
    """

    def __init__(self):
        # TODO: https://sourceware.org/elfutils/
        # TODO: https://sourceware.org/elfutils/ftp/0.186/
        # TODO: these depend on libdebuginfod (=dummy is an option?)
        super().__init__({}, {}, {})

    def _get(self) -> None:
        bk: Path = native / "backward-cpp"
        assert bk.exists(), "Backward is missing; run: git submodule init --recursive"
        assert (bk / "LICENSE.txt").exists(), "Backward missing license"

    def _license(self) -> None:
        pass  # Nothing to install


class Pybind11(Library):
    """
    A class used to manage the backward dependency
    """

    def __init__(self):
        super().__init__({}, {}, {})

    def _get(self) -> None:
        root: Path = native / "pybind11"
        assert root.exists(), "pybind11 is missing; run: git submodule init --recursive"
        assert (root / "LICENSE").exists(), "pybind11 missing license"

    def _license(self):
        pass  # Nothing to install


class Clari(Library):
    """
    A class to manage Clari
    """

    # Constants
    build_dir: Path = native / "build"
    _lib = SharedLib(clari, build_dir)
    _out_native_src: Path = BuiltLib.install_dir / "cpp"
    _binder: Path = native / "src" / "api" / "binder"
    # Docs constants
    _docs_dir: Path = build_dir / "docs"  # Must be in build_dir

    def __init__(self,
                 *,
                 api: bool,
                 no_build: bool = False,
                 no_lib: bool = False,
                 docs: bool = False,
                 debug: bool = False,
                 tests: bool = False):
        # Options
        self._build_lib: bool = not no_lib
        self._build_tests: bool = tests
        self._build_debug: bool = debug
        self._build_doc: bool = docs
        self._build_api: bool = api
        self._no_build: bool = no_build
        # Config
        chk: Dict[str, Path] = {} if (self._build_tests or self._build_doc) else {
            self._lib.name: self._lib,
            "C++ Source files": self._out_native_src
        }
        super().__init__({}, chk, chk, Boost(), Z3(), Pybind11(), Backward())

    def _cmake_args(self) -> List[str]:
        """
        Create arguments to pass to cmake for configuring clari
        """
        z3_built: Optional[Path] = Z3.lib.find_built()
        assert z3_built is not None, "z3 was not built"
        config: Dict[str, Union[Path, bool, str, None]] = {
            "VERSION": version,
            "CLARICPP": clari,  # TODO: clari
            # Build options
            "BUILD_TESTS": self._build_tests,
            "BUILD_DOC": self._build_doc,
            "BUILD_API": self._build_api,
            # Debug options
            "CONSTANT_LOG_LEVEL": not self._build_debug,
            "DEFAULT_RELEASE_LOG_LEVEL": "critical",
            "CMAKE_BUILD_TYPE": "Debug" if self._build_debug else "Release",
            # Backtrace options
            "WARN_BACKWARD_LIMITATIONS": True,
            "REQUIRE_BACKWARD_BACKEND": False,
            # Disable options
            "CPP_CHECK": False,
            "CLANG_TIDY": False,
            "ENABLE_MEMCHECK": False,
            "LWYU": False,
            # Library config
            "GMPDIR": GMP.lib_dir,
            "GMP_INCLUDE_DIR": GMP.include_dir,
            "Boost_INCLUDE_DIRS": Boost.root,
            "Z3_ACQUISITION_MODE": "PATH",
            "Z3_INCLUDE_DIR": Z3.include_dir,
            "Z3_LIB": z3_built,
        }
        for i, k in config.items():
            if isinstance(k, bool):
                config[i] = "ON" if k else "OFF"
            elif k is None:
                config[i] = ""
        return [f"-D{i}={k}" for i, k in config.items()]

    def _build(self) -> None:
        self.build_dir.mkdir(exist_ok=True)
        # CMake
        print("Configuring...")
        with chdir(self.build_dir):
            run_cmd_no_fail(find_exe("cmake"), *self._cmake_args(), native)
        # Build
        if not self._no_build:
            # Order matters (for cleaner output)
            options: Tuple[str] = (
                (self._build_lib, clari),
                (self._build_tests, "unit_tests"),
                (self._build_doc, "docs"),
            )
            targets: List[str] = [i[1] for i in options if i[0]]
            with chdir(self.build_dir):
                for i in targets:
                    build_cmake_target(i)
                if self._build_doc:
                    print(f"Docs built in: {self._docs_dir}")

    @classmethod
    def run_tests(cls) -> None:  # Warning: tests should be built before calling this
        with chdir(cls.build_dir):
            run_cmd_no_fail(find_exe("ctest"), f"-j{max(cpu_count() - 1, 1)}", ".")

    def _license(self) -> None:
        pass  # Same as main project

    def _install(self) -> None:
        if self._build_lib:
            self._lib.install()
        if not self._out_native_src.exists():
            def ign(d: str, fs: List[str]) -> Set[str]:
                keep = shutil.ignore_patterns("*.cpp", "*.hpp", "*.c", "*.h")(d, fs)
                bad = {i for i in fs if i not in keep and not Path(d, i).is_dir()}
                return bad | {i for i in fs if Path(d, i) == self._binder}

            # Parent dir
            parent = self._out_native_src.parent
            if not parent.exists():
                print(f"Creating {self._lic_d}")
                self.parent.mkdir(parents=True)
            # Generate output
            tmp = Path(tempfile.mkdtemp())
            print(f"Generating output source in: {tmp}")
            shutil.copytree(native / "src", tmp / "src", ignore=ign)
            # Install
            print("Installing output source...")
            tmp.rename(self._out_native_src)

    def _clean(self, level: CleanLevel) -> None:
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
            shutil.rmtree(self._out_native_src, ignore_errors=True)
        if level.implies(CleanLevel.BUILT_LIBS):
            self._lib.clean_build()
        if level.implies(CleanLevel.BUILD):
            if (self.build_dir / "Makefile").exists():
                with chdir(self.build_dir):
                    build_cmake_target("clean")
            if self.build_dir.exists():
                shutil.rmtree(self.build_dir, ignore_errors=True)


######################################################################
#                             setuptools                             #
######################################################################


class SDist(SDistOriginal):
    def run(self):
        self.execute(lambda: Clari(api=True).get(), (),
                     msg="Getting build source dependencies")
        super().run()


class Native(Command):
    description: str = "Build native components"
    cmake_msg: str = "Do not build any Clari objects, stop after running cmake"
    docs_msg: str = "Build Clari docs; if --test builds test docs also; if not --no-api build API docs also"
    user_options = [
        ("no-install", None, "Do not install built libraries"),
        ("no-build", None, cmake_msg),
        ("no-lib", None, "Do not build the Clari library"),
        ("no-api", None, "Do not build the Clari API"),
        ("docs", None, docs_msg),
        ("override", None, "Ignore options sanity checks. Do not do this"),
        ("tests", "t", "Build Clari unit tests"),
        ("run-tests", None, "Run Clari tests"),
        ("debug", "d", "Prefers debug mode to release mode while building"),
        ("clean=", "c", "Runs clean at the given level first"),
    ]

    def initialize_options(self) -> None:
        raw: List[str] = [i for i in self.user_options if "=" not in i]  # Bools only
        self.raw = [i[0].replace("-", "_") for i in raw]
        for i in self.raw:
            setattr(self, i, None)
        self.clean: Optional[CleanLevel] = None  # We will put this in args later

    def finalize_options(self) -> None:
        # Namespace args and make them bools here
        args: Dict[str, Any] = {i: (getattr(self, i) is not None) for i in self.raw}
        # Add clean to args and freeze arg keys
        if self.clean is not None:
            self.clean: CleanLevel = to_clean_lvl(self.clean)
        args["clean"]: bool = self.clean
        self.args = JDict(args)
        # Error checking + cleanup
        for i in self.args:
            delattr(self, i)
        if self.args.no_lib and not self.args.no_build:
            print("Warning: --no-lib has no effect given --no-build")
        msgs: List[str] = []
        if self.args.no_build and not self.args.no_install:
            msgs.append("--no-build will likely fail without --no-install")
        if self.args.run_test and self.args.no_build:
            msgs.append("--run-tests will likely fail without --no-build")
        if self.args.run_test and not self.args.tests:
            raise RuntimeError("--run-tests will likely fail without --tests")
        if self.args.no_lib and not self.args.no_api:
            msgs.append("--no-lib will likely fail without --no-api; unless --no-build is passed")
        if self.args.no_lib and self.args.tests:
            msgs.append("--no-lib will likely fail with --tests; unless --no-build is passed")
        if self.args.no_lib and self.args.run_tests:
            msgs.append("--no-lib will likely fail with --run_tests")
        # Allow sanity check override
        if len(msgs) > 0:
            msg: str = "Options sanity check errors:\n  - " + "\n  - ".join(msgs)
            if not self.args.override:
                raise RuntimeError(msg)
            print(f"Overriding o{msg[1:]}")

    def run(self) -> None:
        # Construct the main class and determine the function name
        wanted: Tuple[str] = ("no_lib", "docs", "tests", "debug", "no_build")
        params: Dict[str, str] = {i: k for i, k in self.args.items() if i in wanted}
        instance = Clari(**params, api=not self.args.no_api)
        fname: str = "build" if self.args.no_install else "install"
        # Message
        msg: str = "Building native components"
        options: List[str] = [f"--{i}".replace("_", "-") for i, k in self.args.items() if k]
        if len(options) > 0:
            msg += " with options: " + " ".join(options)
        # Run
        if self.args.clean is not None:
            self.execute(lambda: instance.clean(self.args.clean), (),
                         msg=f"Cleaning Clari at level: {self.args.clean.name}")
        self.execute(lambda: getattr(instance, fname)(), (), msg=msg)
        if self.args.run_tests:
            self.execute(instance.run_tests, (), msg="Running native tests")


class Build(BuildOriginal):
    def run(self):
        self.run_command("native")
        super().run()


class Clean(Command):
    user_options = [("level=", "l", "Clean")]

    def initialize_options(self) -> None:
        self.level: str = "GET"

    def finalize_options(self) -> None:
        self.lvl: CleanLevel = to_clean_lvl(self.level)

    def run(self):
        self.execute(lambda: Clari(api=True).clean(self.lvl), (),
                     msg=f"Cleaning Clari at level: {self.lvl.name}")


if __name__ == "__main__":
    setup(cmdclass={
        "sdist": SDist,
        "build": Build,
        # Custom commands
        "native": Native,
        "clean": Clean,
    })
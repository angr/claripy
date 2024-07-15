use std::borrow::Cow;

use pyo3::{
    exceptions::PyValueError,
    prelude::*,
    types::{PyAnyMethods, PyBool, PyBytes, PyDict, PyFloat, PyInt, PySet, PyString, PyTuple},
};

#[pyclass(weakref)]
pub struct ASTCacheKey {
    #[pyo3(get)]
    ast: PyObject,
    #[pyo3(get)]
    hash: isize,
}

#[pymethods]
impl ASTCacheKey {
    #[new]
    pub fn new(ast: Bound<PyAny>) -> PyResult<Self> {
        Ok(ASTCacheKey {
            hash: ast.as_any().hash()?,
            ast: ast.into(),
        })
    }

    pub fn __hash__(&self) -> isize {
        self.hash
    }

    pub fn __eq__(&self, other: &Self) -> bool {
        self.hash == other.hash
    }

    pub fn __repr__(&self) -> String {
        format!("<Key {} >", self.ast)
    }
}

#[pyclass(subclass, weakref)]
pub struct Base {
    // Hashcons
    #[pyo3(get, set)]
    op: String,
    #[pyo3(get, set)]
    args: Py<PyTuple>,
    #[pyo3(get, set)]
    length: usize,
    #[pyo3(get, set)]
    variables: PyObject, // TODO: This should be a HashSet, leave opaque for now
    #[pyo3(get, set)]
    symbolic: bool,
    #[pyo3(get, set)]
    annotations: Py<PyTuple>,

    // Not Hashcons
    #[pyo3(get)]
    depth: usize,

    #[pyo3(get, set)]
    _hash: Option<isize>,
    #[pyo3(get, set)]
    _simplified: Option<PyObject>,
    #[pyo3(get, set)]
    _cache_key: Option<Py<ASTCacheKey>>,
    #[pyo3(get, set)]
    _cached_encoded_name: Option<PyObject>,
    #[pyo3(get, set)]
    _errored: Py<PySet>,
    #[pyo3(get, set)]
    _eager_backends: Option<PyObject>,
    #[pyo3(get, set)]
    _excavated: Option<PyObject>,
    #[pyo3(get, set)]
    _burrowed: Option<PyObject>,
    #[pyo3(get, set)]
    _uninitialized: Option<PyObject>,
    #[pyo3(get, set)]
    _uc_alloc_depth: Option<PyObject>,
    #[pyo3(get, set)]
    _uneliminatable_annotations: Option<PyObject>,
    #[pyo3(get, set)]
    _relocatable_annotations: Option<PyObject>,
}

#[pymethods]
impl Base {
    #[new]
    #[pyo3(signature = (
        op,
        args,
        length,
        variables,
        symbolic,
        annotations=None,
        simplified=None,
        errored=None,
        eager_backends=None,
        uninitialized=None,
        uc_alloc_depth=None,
        encoded_name=None,
        depth=None,
        uneliminatable_annotations=None,
        relocatable_annotations=None
    ))]
    fn new(
        py: Python,
        op: String,
        args: Bound<PyTuple>,
        length: usize,
        variables: Bound<PyAny>,
        symbolic: bool,
        annotations: Option<Bound<PyTuple>>,
        // New stuff
        simplified: Option<Bound<PyAny>>,
        errored: Option<Bound<PySet>>,
        eager_backends: Option<Bound<PyAny>>,
        uninitialized: Option<Bound<PyAny>>,
        uc_alloc_depth: Option<Bound<PyAny>>,
        encoded_name: Option<Bound<PyAny>>,
        depth: Option<usize>,
        uneliminatable_annotations: Option<Bound<PyAny>>,
        relocatable_annotations: Option<Bound<PyAny>>,
    ) -> PyResult<Self> {
        if args.len() == 0 {
            return Err(PyValueError::new_err("AST with no arguments!")); // TODO: This should be a custom error
        }

        let depth = depth.unwrap_or(
            *args
                .iter()
                .map(|arg| {
                    arg.getattr("depth")
                        .and_then(|p| p.extract::<usize>())
                        .or_else(|_| Ok(1))
                })
                .collect::<Result<Vec<usize>, PyErr>>()?
                .iter()
                .max()
                .unwrap_or(&0)
                + 1,
        );

        Ok(Base {
            op,
            args: args.into(),
            length,
            variables: variables.into(),
            symbolic,
            annotations: annotations
                .unwrap_or_else(|| PyTuple::empty_bound(py))
                .into(),

            depth,

            _hash: None,
            _simplified: simplified.map(|s| s.into()),
            _cache_key: None,
            _cached_encoded_name: encoded_name.map(|s| s.into()),
            _errored: errored.unwrap_or(PySet::empty_bound(py)?).into(),
            _eager_backends: eager_backends.map(|s| s.into()),
            _excavated: None,
            _burrowed: None,
            _uninitialized: uninitialized.map(|s| s.into()),
            _uc_alloc_depth: uc_alloc_depth.map(|s| s.into()),
            _uneliminatable_annotations: uneliminatable_annotations.map(|s| s.into()),
            _relocatable_annotations: relocatable_annotations.map(|s| s.into()),
        })
    }

    #[staticmethod]
    fn _arg_serialize<'py>(
        py: Python<'py>,
        arg: Bound<'_, PyAny>,
    ) -> PyResult<Option<Cow<'py, [u8]>>> {
        if arg.is_none() {
            return Ok(Some(Cow::from(vec![b'\x0f'])));
        }
        if arg.is(&*PyBool::new_bound(py, true)) {
            return Ok(Some(Cow::from(vec![b'\x1f'])));
        }
        if arg.is(&*PyBool::new_bound(py, false)) {
            return Ok(Some(Cow::from(vec![b'\x2e'])));
        }
        if arg.is_instance(&py.get_type_bound::<PyInt>())? {
            let arg = arg.downcast::<PyInt>()?.extract::<i128>()?;
            let mut result = Vec::new();
            if arg < 0 {
                result.push(b'-');
                if arg >= -0x7FFF {
                    result.extend_from_slice(&(arg as i16).to_le_bytes());
                } else if arg >= -0x7FFF_FFFF {
                    result.extend_from_slice(&(arg as i32).to_le_bytes());
                } else if arg >= -0x7FFF_FFFF_FFFF_FFFF {
                    result.extend_from_slice(&(arg as i64).to_le_bytes());
                } else {
                    return Ok(None);
                }
            } else {
                if arg <= 0xFFFF {
                    result.extend_from_slice(&(arg as i16).to_le_bytes());
                } else if arg <= 0xFFFF_FFFF {
                    result.extend_from_slice(&(arg as i32).to_le_bytes());
                } else if arg <= 0xFFFF_FFFF_FFFF_FFFF {
                    result.extend_from_slice(&(arg as i64).to_le_bytes());
                } else {
                    return Ok(None);
                }
            }
            return Ok(Some(Cow::from(result)));
        }
        if arg.is_instance(&py.get_type_bound::<PyString>())? {
            let arg: String = arg.downcast::<PyString>()?.extract()?;
            return Ok(Some(Cow::from(arg.into_bytes())));
        }
        if arg.is_instance(&py.get_type_bound::<PyFloat>())? {
            return Ok(Some(Cow::from(Vec::from(
                arg.downcast::<PyFloat>()?.extract::<f32>()?.to_le_bytes(),
            ))));
        }
        if arg.is_instance(&py.get_type_bound::<PyTuple>())? {
            let mut result = Vec::new();
            for item in arg.downcast::<PyTuple>()?.iter() {
                if let Some(sub_result) = Self::_arg_serialize(py, item)? {
                    result.extend(sub_result.iter());
                } else {
                    return Ok(None); // Do we really want to return None here?
                }
            }
            return Ok(Some(Cow::from(result)));
        }
        Ok(None)
    }

    #[staticmethod]
    fn _ast_serialize<'py>(
        py: Python<'py>,
        op: String,
        args_tuple: Bound<'_, PyTuple>,
        keywords: Bound<'_, PyDict>, // TODO: This should be a struct or seperate args
    ) -> PyResult<Option<Cow<'py, [u8]>>> {
        let serailized_args = match Base::_arg_serialize(py, args_tuple.into_any())? {
            Some(args) => args,
            None => return Ok(None),
        };

        let length = match keywords.contains("length")? {
            true => match Base::_arg_serialize(py, keywords.get_item("length")?.unwrap())? {
                Some(length) => length,
                None => return Ok(None),
            },
            false => Cow::from(Vec::from(b"none")),
        };

        // get_item was unchecked in the python version too
        let variables = (keywords.get_item("variables")?.unwrap().hash()? as u64).to_le_bytes();
        // this one was unchecked too
        let symbolic = match keywords.get_item("symbolic")?.unwrap().is_truthy()? {
            true => Cow::from(Vec::from(b"\x01")),
            false => Cow::from(Vec::from(b"\x00")),
        };
        let annotations = match keywords.get_item("annotations")? {
            Some(item) => Cow::from(Vec::from((item.hash()? as u64).to_le_bytes())),
            None => Cow::from(Vec::from(b"\xf9")),
        };

        Ok(Some(Cow::from(
            [
                op.as_bytes(),
                &serailized_args,
                &length,
                &variables,
                &symbolic,
                &annotations,
            ]
            .concat(),
        )))
    }

    #[staticmethod]
    fn _calc_hash<'py>(
        py: Python<'py>,
        op: String,
        args: Bound<PyTuple>,
        keywords: Bound<PyDict>,
    ) -> PyResult<isize> {
        let mut args_tuple = Vec::new();
        for arg in args.iter() {
            if arg.is_instance(&py.get_type_bound::<PyInt>())?
                || arg.is_instance(&py.get_type_bound::<PyFloat>())?
            {
                args_tuple.push(arg);
            } else {
                if arg.hasattr("_hash")? {
                    args_tuple.push(
                        arg.getattr("_hash")?
                            .downcast::<PyInt>()
                            .unwrap()
                            .clone()
                            .into_any(),
                    );
                } else {
                    args_tuple.push(
                        // Call hash on the object
                        arg.call_method0("__hash__")?
                            .downcast::<PyInt>()
                            .unwrap()
                            .clone()
                            .into_any(),
                    );
                }
            }
        }

        let to_hash = match Base::_ast_serialize(py, op.clone(), args, keywords.clone())? {
            Some(to_hash) => to_hash,
            None => {
                let hash_tuple: Bound<PyTuple> = PyTuple::new_bound(
                    py,
                    vec![
                        op.to_object(py).bind(py).as_ref(),
                        args_tuple.to_object(py).bind(py).as_ref(),
                        keywords
                            .get_item("length")?
                            .unwrap_or(py.None().into_bound(py))
                            .str()?
                            .as_ref(),
                        keywords
                            .get_item("variables")?
                            .unwrap() // Unchecked unwrap in python version
                            .hash()?
                            .to_object(py)
                            .bind(py),
                        keywords.get_item("symbolic")?.unwrap().as_ref(), // Unchecked unwrap in python version
                        keywords
                            .get_item("annotations")?
                            .unwrap_or(py.None().into_bound(py))
                            .hash()?
                            .to_object(py)
                            .bind(py),
                    ],
                );
                Cow::from(Vec::from(
                    py.import_bound("pickle")?
                        .getattr("dumps")?
                        .call1(PyTuple::new_bound(py, vec![&hash_tuple]))?
                        .downcast_into::<PyBytes>()?
                        .as_bytes(),
                ))
            }
        };
        Ok(isize::from_be_bytes(
            (md5::compute(to_hash).0)[..8].try_into().unwrap(),
        ))
    }
}

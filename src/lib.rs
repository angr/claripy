use pyo3::{prelude::*, types::PyTuple};

#[pyclass(subclass, weakref)]
struct Base {
    // Hashcons
    #[pyo3(get, set)]
    op: String,
    #[pyo3(get, set)]
    args: Py<PyTuple>,
    #[pyo3(get, set)]
    length: PyObject,
    #[pyo3(get, set)]
    variables: PyObject, // TODO: This should be a HashSet, leave opaque for now
    #[pyo3(get, set)]
    symbolic: bool,
    #[pyo3(get, set)]
    annotations: Py<PyTuple>,

    // Not Hashcons
    #[pyo3(get, set)]
    simplifiable: Option<PyObject>,
    #[pyo3(get, set)]
    depth: Option<PyObject>,

    #[pyo3(get, set)]
    _hash: Option<PyObject>,
    #[pyo3(get, set)]
    _simplified: Option<PyObject>,
    #[pyo3(get, set)]
    _cache_key: Option<PyObject>,
    #[pyo3(get, set)]
    _cached_encoded_name: Option<PyObject>,
    #[pyo3(get, set)]
    _errored: Option<PyObject>,
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
    #[pyo3(signature = (op, args, length, variables, symbolic, annotations))]
    fn new(
        py: Python,
        op: String,
        args: Py<PyTuple>,
        length: PyObject,
        variables: PyObject,
        symbolic: bool,
        annotations: Py<PyTuple>,
    ) -> PyResult<Self> {
        Ok(Base {
            op,
            args,
            length,
            variables,
            symbolic,
            annotations,

            simplifiable: None,
            depth: None,

            _hash: None,
            _simplified: None,
            _cache_key: None,
            _cached_encoded_name: None,
            _errored: None,
            _eager_backends: None,
            _excavated: None,
            _burrowed: None,
            _uninitialized: None,
            _uc_alloc_depth: None,
            _uneliminatable_annotations: None,
            _relocatable_annotations: None,
        })
    }
}

#[pymodule]
fn clarirs(_py: Python, m: Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Base>()?;
    Ok(())
}

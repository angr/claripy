use std::collections::HashSet;

use pyo3::{prelude::*, types::PyTuple};

#[pyclass(subclass)]
struct Base {
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
}

#[pymethods]
impl Base {
    #[new]
    #[pyo3(signature = (op, args, length, variables, symbolic, annotations))]
    fn new(
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
        })
    }
}

#[pymodule]
fn clarirs(_py: Python, m: Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Base>()?;
    Ok(())
}

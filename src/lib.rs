use pyo3::prelude::*;


#[pyclass(subclass)]
struct Base {}

#[pymethods]
impl Base {
    #[new]
    fn new() -> Self {
        Base {}
    }
}

#[pymodule]
fn clarirs(_py: Python, m: Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Base>()?;
    Ok(())
}

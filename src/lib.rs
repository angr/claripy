mod ast;

use pyo3::prelude::*;

#[pymodule]
fn clarirs(_py: Python, m: Bound<PyModule>) -> PyResult<()> {
    m.add_class::<ast::base::Base>()?;
    Ok(())
}

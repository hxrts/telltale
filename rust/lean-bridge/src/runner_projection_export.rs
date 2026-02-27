use super::*;
use std::io::Write;

impl LeanRunner {
    /// Default path to the VM runner binary (relative to workspace root).
    pub const VM_RUNNER_BINARY_PATH: &'static str = "lean/.lake/build/bin/vm_runner";

    /// Get the full path to the VM runner binary.
    fn get_vm_runner_path() -> Option<PathBuf> {
        Self::find_workspace_root()
            .map(|root| root.join(Self::VM_RUNNER_BINARY_PATH))
            .filter(|p| p.exists())
    }

    /// Check if the validator binary is available for projection export.
    #[must_use]
    pub fn is_projection_available() -> bool {
        Self::is_available()
    }

    /// Project a GlobalType for a list of roles using the Lean validator export mode.
    ///
    /// Writes the GlobalType JSON to a temp file, runs
    /// `telltale_validator --export-all-projections`, and parses the projections.
    ///
    /// # Output format (parsed from output file)
    ///
    /// ```json
    /// {
    ///   "success": true,
    ///   "projections": { "A": { "kind": "send", ... }, "B": { "kind": "recv", ... } }
    /// }
    /// ```
    pub fn project(
        &self,
        global_json: &Value,
        roles: &[String],
    ) -> Result<std::collections::HashMap<String, Value>, LeanRunnerError> {
        let mut input_file = NamedTempFile::new()?;
        serde_json::to_writer(&mut input_file, global_json)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;
        input_file.flush()?;

        let output_file = NamedTempFile::new()?;
        let output_path = output_file.path().to_path_buf();

        let output = Command::new(&self.binary_path)
            .arg("--export-all-projections")
            .arg(input_file.path())
            .arg("--output")
            .arg(&output_path)
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let output_contents = std::fs::read_to_string(&output_path)?;
        let payload: Value = serde_json::from_str(&output_contents)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        if let Some(false) = payload.get("success").and_then(|v| v.as_bool()) {
            let err = payload
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("Lean export failed");
            return Err(LeanRunnerError::ParseError(err.to_string()));
        }

        let projections_val = payload
            .get("projections")
            .ok_or_else(|| LeanRunnerError::ParseError("missing projections field".to_string()))?;

        let projections_map = match projections_val {
            Value::Object(map) => map
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect::<std::collections::HashMap<_, _>>(),
            Value::Array(items) => {
                let mut out = std::collections::HashMap::new();
                for item in items {
                    let obj = item.as_object().ok_or_else(|| {
                        LeanRunnerError::ParseError("invalid projection entry".to_string())
                    })?;
                    let role = obj.get("role").and_then(|v| v.as_str()).ok_or_else(|| {
                        LeanRunnerError::ParseError("missing role in projection".to_string())
                    })?;
                    let local = obj
                        .get("local_type")
                        .or_else(|| obj.get("localType"))
                        .ok_or_else(|| {
                            LeanRunnerError::ParseError(
                                "missing local_type in projection".to_string(),
                            )
                        })?;
                    out.insert(role.to_string(), local.clone());
                }
                out
            }
            _ => {
                return Err(LeanRunnerError::ParseError(
                    "invalid projections format".to_string(),
                ))
            }
        };

        if roles.is_empty() {
            return Ok(projections_map);
        }

        let mut selected = std::collections::HashMap::new();
        for role in roles {
            let projection = projections_map.get(role).ok_or_else(|| {
                LeanRunnerError::ParseError(format!("missing projection for role {role}"))
            })?;
            selected.insert(role.clone(), projection.clone());
        }
        Ok(selected)
    }

    /// Check conservative async-subtyping in Lean.
    ///
    /// Invokes the Lean validator with `--check-async-subtype` mode and returns
    /// whether the subtype relation holds.
    pub fn check_async_subtype(
        &self,
        subtype_json: &Value,
        supertype_json: &Value,
    ) -> Result<bool, LeanRunnerError> {
        let subtype_file = NamedTempFile::new()?;
        let supertype_file = NamedTempFile::new()?;
        let output_file = NamedTempFile::new()?;

        std::fs::write(
            subtype_file.path(),
            serde_json::to_string_pretty(subtype_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;
        std::fs::write(
            supertype_file.path(),
            serde_json::to_string_pretty(supertype_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;

        let output = Command::new(&self.binary_path)
            .arg("--check-async-subtype")
            .arg(subtype_file.path())
            .arg(supertype_file.path())
            .arg("--output")
            .arg(output_file.path())
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let output_content = std::fs::read_to_string(output_file.path())?;
        let payload: Value = serde_json::from_str(&output_content)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        let success = payload
            .get("success")
            .and_then(|v| v.as_bool())
            .ok_or_else(|| LeanRunnerError::ParseError("missing success field".to_string()))?;
        if !success {
            let err = payload
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("Lean async-subtyping check failed");
            return Err(LeanRunnerError::ParseError(err.to_string()));
        }

        let result = payload
            .get("result")
            .and_then(|v| v.as_bool())
            .ok_or_else(|| LeanRunnerError::ParseError("missing result field".to_string()))?;
        Ok(result)
    }

    /// Check conservative orphan-freedom in Lean.
    ///
    /// Invokes the Lean validator with `--check-orphan-free` mode and returns
    /// whether the orphan-freedom predicate holds.
    pub fn check_orphan_free(&self, local_json: &Value) -> Result<bool, LeanRunnerError> {
        let local_file = NamedTempFile::new()?;
        let output_file = NamedTempFile::new()?;

        std::fs::write(
            local_file.path(),
            serde_json::to_string_pretty(local_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;

        let output = Command::new(&self.binary_path)
            .arg("--check-orphan-free")
            .arg(local_file.path())
            .arg("--output")
            .arg(output_file.path())
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let output_content = std::fs::read_to_string(output_file.path())?;
        let payload: Value = serde_json::from_str(&output_content)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        let success = payload
            .get("success")
            .and_then(|v| v.as_bool())
            .ok_or_else(|| LeanRunnerError::ParseError("missing success field".to_string()))?;
        if !success {
            let err = payload
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("Lean orphan-free check failed");
            return Err(LeanRunnerError::ParseError(err.to_string()));
        }

        let result = payload
            .get("result")
            .and_then(|v| v.as_bool())
            .ok_or_else(|| LeanRunnerError::ParseError("missing result field".to_string()))?;
        Ok(result)
    }

    /// Run one or more choreographies on the Lean VM at a given concurrency level.
    ///
    /// # Errors
    ///
    /// Returns an error if the VM runner binary is missing, the process fails,
    /// or the output is not valid JSON.
    pub fn run_vm_protocol(
        &self,
        choreographies: &[ChoreographyJson],
        concurrency: usize,
        max_steps: usize,
    ) -> Result<Value, LeanRunnerError> {
        let vm_path = Self::get_vm_runner_path().ok_or_else(|| {
            LeanRunnerError::BinaryNotFound(PathBuf::from(Self::VM_RUNNER_BINARY_PATH))
        })?;

        let input = serde_json::json!({
            "schema_version": crate::schema::default_schema_version(),
            "choreographies": choreographies,
            "concurrency": concurrency,
            "max_steps": max_steps
        });
        let input_str = serde_json::to_string(&input)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        let mut child = Command::new(&vm_path)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(input_str.as_bytes())
                .map_err(LeanRunnerError::TempFileError)?;
        }

        let output = child.wait_with_output()?;
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        if !output.status.success() {
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let json: Value = serde_json::from_str(&stdout)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;
        Ok(json)
    }

    /// Export Lean's projection for a single role.
    ///
    /// Invokes the Lean runner with `--export-projection` mode and returns
    /// the JSON result containing either the computed LocalTypeR or an error.
    pub fn export_projection(
        &self,
        global_json: &Value,
        role: &str,
    ) -> Result<Value, LeanRunnerError> {
        let input_file = NamedTempFile::new()?;
        let output_file = NamedTempFile::new()?;

        std::fs::write(
            input_file.path(),
            serde_json::to_string_pretty(global_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;

        let output = Command::new(&self.binary_path)
            .arg("--export-projection")
            .arg(input_file.path())
            .arg("--role")
            .arg(role)
            .arg("--output")
            .arg(output_file.path())
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let result_content = std::fs::read_to_string(output_file.path())?;
        let result: Value = serde_json::from_str(&result_content)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;
        Ok(result)
    }

    /// Export Lean's projection for all roles in a GlobalType.
    ///
    /// Invokes the Lean runner with `--export-all-projections` mode and returns
    /// the JSON result containing projections for all roles.
    pub fn export_all_projections(&self, global_json: &Value) -> Result<Value, LeanRunnerError> {
        let input_file = NamedTempFile::new()?;
        let output_file = NamedTempFile::new()?;

        std::fs::write(
            input_file.path(),
            serde_json::to_string_pretty(global_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;

        let output = Command::new(&self.binary_path)
            .arg("--export-all-projections")
            .arg(input_file.path())
            .arg("--output")
            .arg(output_file.path())
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let result_content = std::fs::read_to_string(output_file.path())?;
        let result: Value = serde_json::from_str(&result_content)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        Ok(result)
    }
}

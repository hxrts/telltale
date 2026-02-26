use super::*;

impl EquivalenceChecker {
    /// Check a Rust projection against a golden file.
    ///
    /// This is the fast path - no Lean required.
    pub fn check_projection_against_golden(
        &self,
        test_name: &str,
        global: &GlobalType,
        role: &str,
    ) -> Result<EquivalenceResult, EquivalenceError> {
        let golden_path = self
            .config
            .golden_dir
            .join(test_name)
            .join(format!("{}.expected.json", role));

        let golden_content = std::fs::read_to_string(&golden_path)
            .map_err(|_| EquivalenceError::GoldenNotFound(golden_path.clone()))?;
        let expected: Value = serde_json::from_str(&golden_content)?;

        let rust_local = project(global, role)?;
        let rust_output = local_to_json(&rust_local);
        self.compare_local_types(role, &rust_output, &expected)
    }

    /// Load a golden bundle for a test case.
    pub fn load_golden_bundle(&self, test_name: &str) -> Result<GoldenBundle, EquivalenceError> {
        let test_dir = self.config.golden_dir.join(test_name);

        let input_path = test_dir.join("input.json");
        let input: Value = serde_json::from_str(
            &std::fs::read_to_string(&input_path)
                .map_err(|_| EquivalenceError::GoldenNotFound(input_path))?,
        )?;

        let mut projections = HashMap::new();
        for entry in std::fs::read_dir(&test_dir)? {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().to_string();
            if name.ends_with(".expected.json") {
                let role = name.trim_end_matches(".expected.json").to_string();
                let content = std::fs::read_to_string(entry.path())?;
                let value: Value = serde_json::from_str(&content)?;
                projections.insert(role, value);
            }
        }

        Ok(GoldenBundle {
            schema_version: crate::schema::default_schema_version(),
            input,
            projections,
            coherence: None,
        })
    }

    /// Check all projections in a golden bundle.
    pub fn check_all_projections_against_golden(
        &self,
        test_name: &str,
        global: &GlobalType,
    ) -> Result<Vec<EquivalenceResult>, EquivalenceError> {
        let bundle = self.load_golden_bundle(test_name)?;
        let mut results = Vec::new();

        for (role, expected) in &bundle.projections {
            let rust_local = project(global, role)?;
            let rust_output = local_to_json(&rust_local);
            let result = self.compare_local_types(role, &rust_output, expected)?;
            results.push(result);
        }

        Ok(results)
    }

    /// Generate golden files from live Lean for a GlobalType.
    ///
    /// Returns the bundle that would be written.
    pub fn generate_golden_bundle(
        &self,
        global: &GlobalType,
    ) -> Result<GoldenBundle, EquivalenceError> {
        let runner = self
            .runner
            .as_ref()
            .ok_or(EquivalenceError::LeanNotAvailable)?;

        let global_json = global_to_json(global);
        let lean_output = runner.export_all_projections(&global_json)?;

        if lean_output["success"].as_bool() != Some(true) {
            let err = lean_output["error"].to_string();
            return Err(EquivalenceError::ParseError(format!(
                "Lean projections failed: {}",
                err
            )));
        }

        let projections = Self::parse_projections_map(&lean_output)?;

        Ok(GoldenBundle {
            schema_version: crate::schema::default_schema_version(),
            input: global_json,
            projections,
            coherence: None,
        })
    }

    /// Write a golden bundle to disk.
    pub fn write_golden_bundle(
        &self,
        test_name: &str,
        bundle: &GoldenBundle,
    ) -> Result<(), EquivalenceError> {
        let test_dir = self.config.golden_dir.join(test_name);
        std::fs::create_dir_all(&test_dir)?;

        let input_path = test_dir.join("input.json");
        std::fs::write(input_path, serde_json::to_string_pretty(&bundle.input)?)?;

        for (role, local_type) in &bundle.projections {
            let path = test_dir.join(format!("{}.expected.json", role));
            std::fs::write(path, serde_json::to_string_pretty(local_type)?)?;
        }

        Ok(())
    }

    /// Check if golden files are up-to-date with current Lean.
    ///
    /// Returns a list of test cases with drift.
    pub fn check_golden_drift(&self) -> Result<Vec<String>, EquivalenceError> {
        let runner = self
            .runner
            .as_ref()
            .ok_or(EquivalenceError::LeanNotAvailable)?;

        let projection_dir = self.config.golden_dir.clone();
        if !projection_dir.exists() {
            return Ok(vec![]);
        }

        let mut drifted = Vec::new();

        for entry in std::fs::read_dir(&projection_dir)? {
            let entry = entry?;
            if entry.file_type()?.is_dir() {
                let test_name = entry.file_name().to_string_lossy().to_string();
                let input_path = entry.path().join("input.json");
                if !input_path.exists() {
                    continue;
                }

                let input: Value = serde_json::from_str(&std::fs::read_to_string(&input_path)?)?;
                let lean_output = runner.export_all_projections(&input)?;

                if lean_output["success"].as_bool() != Some(true) {
                    continue;
                }

                let projections = match Self::parse_projections_map(&lean_output) {
                    Ok(projections) => projections,
                    Err(_) => continue,
                };

                for (role, fresh) in projections {
                    let golden_path = entry.path().join(format!("{}.expected.json", role));
                    if !golden_path.exists() {
                        drifted.push(format!("{}:{} (missing)", test_name, role));
                        continue;
                    }

                    let golden: Value =
                        serde_json::from_str(&std::fs::read_to_string(&golden_path)?)?;

                    if !self.json_structurally_equal(&golden, &fresh) {
                        drifted.push(format!("{}:{}", test_name, role));
                    }
                }
            }
        }

        Ok(drifted)
    }
}

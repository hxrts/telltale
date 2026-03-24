impl KernelMachine for VM {
    fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        VM::kernel_step_round(self, handler, n)
    }
}

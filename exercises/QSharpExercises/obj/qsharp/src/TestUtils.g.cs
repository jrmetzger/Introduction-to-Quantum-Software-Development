//------------------------------------------------------------------------------
// <auto-generated>                                                             
//     This code was generated by a tool.                                       
//     Changes to this file may cause incorrect behavior and will be lost if    
//     the code is regenerated.                                                 
// </auto-generated>                                                            
//------------------------------------------------------------------------------
#pragma warning disable 436
#pragma warning disable 162
#pragma warning disable 1591
using System;
using Microsoft.Quantum.Core;
using Microsoft.Quantum.Intrinsic;
using Microsoft.Quantum.Simulation.Core;

[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"QSharpExercises.Tests.Utils\",\"Name\":\"GenerateRandomRotation\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"BasicQuantumFunctionality\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs\",\"Position\":{\"Item1\":11,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":33}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"UnitType\"},\"ReturnType\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Double\"}]},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Tests.Utils\",\"Name\":\"GenerateRandomRotation\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs\",\"Position\":{\"Item1\":11,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":33}},\"Documentation\":[]}")]
[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"QSharpExercises.Tests.Utils\",\"Name\":\"ApplyRotation\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"BasicQuantumFunctionality\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs\",\"Position\":{\"Item1\":19,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":24}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"rotation\"]},\"Type\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Double\"}]},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":26},\"Item2\":{\"Line\":1,\"Column\":34}}}]},{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"target\"]},\"Type\":{\"Case\":\"Qubit\"},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":47},\"Item2\":{\"Line\":1,\"Column\":53}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Double\"}]},{\"Case\":\"Qubit\"}]]},\"ReturnType\":{\"Case\":\"UnitType\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Tests.Utils\",\"Name\":\"ApplyRotation\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs\",\"Position\":{\"Item1\":19,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":24}},\"Documentation\":[]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsAdjoint\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Tests.Utils\",\"Name\":\"ApplyRotation\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs\",\"Position\":{\"Item1\":19,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":2,\"Column\":8},\"Item2\":{\"Line\":2,\"Column\":17}},\"Documentation\":[\"automatically generated QsAdjoint specialization for QSharpExercises.Tests.Utils.ApplyRotation\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsControlled\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Tests.Utils\",\"Name\":\"ApplyRotation\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs\",\"Position\":{\"Item1\":19,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":2,\"Column\":8},\"Item2\":{\"Line\":2,\"Column\":17}},\"Documentation\":[\"automatically generated QsControlled specialization for QSharpExercises.Tests.Utils.ApplyRotation\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsControlledAdjoint\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Tests.Utils\",\"Name\":\"ApplyRotation\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs\",\"Position\":{\"Item1\":19,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":2,\"Column\":8},\"Item2\":{\"Line\":2,\"Column\":17}},\"Documentation\":[\"automatically generated QsControlledAdjoint specialization for QSharpExercises.Tests.Utils.ApplyRotation\"]}")]
#line hidden
namespace QSharpExercises.Tests.Utils
{
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs", OperationFunctor.Body, 12, 20)]
    public partial class GenerateRandomRotation : Operation<QVoid, IQArray<Double>>, ICallable
    {
        public GenerateRandomRotation(IOperationFactory m) : base(m)
        {
        }

        String ICallable.Name => "GenerateRandomRotation";
        String ICallable.FullName => "QSharpExercises.Tests.Utils.GenerateRandomRotation";
        protected ICallable<(Double,Double), Double> Microsoft__Quantum__Random__DrawRandomDouble
        {
            get;
            set;
        }

        protected ICallable<QVoid, Double> Microsoft__Quantum__Math__PI
        {
            get;
            set;
        }

        public override Func<QVoid, IQArray<Double>> __Body__ => (__in__) =>
        {
#line 13 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            return new QArray<Double>(Microsoft__Quantum__Random__DrawRandomDouble.Apply((0D, Microsoft__Quantum__Math__PI.Apply(QVoid.Instance))), Microsoft__Quantum__Random__DrawRandomDouble.Apply((0D, (2D * Microsoft__Quantum__Math__PI.Apply(QVoid.Instance)))));
        }

        ;
        public override void __Init__()
        {
            this.Microsoft__Quantum__Random__DrawRandomDouble = this.__Factory__.Get<ICallable<(Double,Double), Double>>(typeof(global::Microsoft.Quantum.Random.DrawRandomDouble));
            this.Microsoft__Quantum__Math__PI = this.__Factory__.Get<ICallable<QVoid, Double>>(typeof(global::Microsoft.Quantum.Math.PI));
        }

        public override IApplyData __DataIn__(QVoid data) => data;
        public override IApplyData __DataOut__(IQArray<Double> data) => data;
        public static System.Threading.Tasks.Task<IQArray<Double>> Run(IOperationFactory __m__)
        {
            return __m__.Run<GenerateRandomRotation, QVoid, IQArray<Double>>(QVoid.Instance);
        }
    }

    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs", OperationFunctor.Body, 20, -1)]
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs", OperationFunctor.Adjoint, 20, -1)]
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs", OperationFunctor.Controlled, 20, -1)]
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs", OperationFunctor.ControlledAdjoint, 20, -1)]
    public partial class ApplyRotation : Unitary<(IQArray<Double>,Qubit)>, ICallable
    {
        public ApplyRotation(IOperationFactory m) : base(m)
        {
        }

        public class In : QTuple<(IQArray<Double>,Qubit)>, IApplyData
        {
            public In((IQArray<Double>,Qubit) data) : base(data)
            {
            }

            System.Collections.Generic.IEnumerable<Qubit> IApplyData.Qubits
            {
                get
                {
                    yield return Data.Item2;
                }
            }
        }

        String ICallable.Name => "ApplyRotation";
        String ICallable.FullName => "QSharpExercises.Tests.Utils.ApplyRotation";
        protected IUnitary<(Double,Qubit)> Microsoft__Quantum__Intrinsic__Rx
        {
            get;
            set;
        }

        protected IUnitary<(Double,Qubit)> Microsoft__Quantum__Intrinsic__Rz
        {
            get;
            set;
        }

        public override Func<(IQArray<Double>,Qubit), QVoid> __Body__ => (__in__) =>
        {
            var (rotation,target) = __in__;
#line 22 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            Microsoft__Quantum__Intrinsic__Rx.Apply((rotation[0L], target));
#line 23 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            Microsoft__Quantum__Intrinsic__Rz.Apply((rotation[1L], target));
#line hidden
            return QVoid.Instance;
        }

        ;
        public override Func<(IQArray<Double>,Qubit), QVoid> __AdjointBody__ => (__in__) =>
        {
            var (rotation,target) = __in__;
#line 20 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            Microsoft__Quantum__Intrinsic__Rz.Adjoint.Apply((rotation[1L], target));
#line 20 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            Microsoft__Quantum__Intrinsic__Rx.Adjoint.Apply((rotation[0L], target));
#line hidden
            return QVoid.Instance;
        }

        ;
        public override Func<(IQArray<Qubit>,(IQArray<Double>,Qubit)), QVoid> __ControlledBody__ => (__in__) =>
        {
            var (__controlQubits__,(rotation,target)) = __in__;
#line 20 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            Microsoft__Quantum__Intrinsic__Rx.Controlled.Apply((__controlQubits__, (rotation[0L], target)));
#line 20 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            Microsoft__Quantum__Intrinsic__Rz.Controlled.Apply((__controlQubits__, (rotation[1L], target)));
#line hidden
            return QVoid.Instance;
        }

        ;
        public override Func<(IQArray<Qubit>,(IQArray<Double>,Qubit)), QVoid> __ControlledAdjointBody__ => (__in__) =>
        {
            var (__controlQubits__,(rotation,target)) = __in__;
#line 20 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            Microsoft__Quantum__Intrinsic__Rz.Adjoint.Controlled.Apply((__controlQubits__, (rotation[1L], target)));
#line 20 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Tests/TestUtils.qs"
            Microsoft__Quantum__Intrinsic__Rx.Adjoint.Controlled.Apply((__controlQubits__, (rotation[0L], target)));
#line hidden
            return QVoid.Instance;
        }

        ;
        public override void __Init__()
        {
            this.Microsoft__Quantum__Intrinsic__Rx = this.__Factory__.Get<IUnitary<(Double,Qubit)>>(typeof(global::Microsoft.Quantum.Intrinsic.Rx));
            this.Microsoft__Quantum__Intrinsic__Rz = this.__Factory__.Get<IUnitary<(Double,Qubit)>>(typeof(global::Microsoft.Quantum.Intrinsic.Rz));
        }

        public override IApplyData __DataIn__((IQArray<Double>,Qubit) data) => new In(data);
        public override IApplyData __DataOut__(QVoid data) => data;
        public static System.Threading.Tasks.Task<QVoid> Run(IOperationFactory __m__, IQArray<Double> rotation, Qubit target)
        {
            return __m__.Run<ApplyRotation, (IQArray<Double>,Qubit), QVoid>((rotation, target));
        }
    }
}
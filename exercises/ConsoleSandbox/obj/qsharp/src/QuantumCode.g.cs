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

[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"QSharpExercises.ConsoleSandbox\",\"Name\":\"RotateAndMeasureQubit\"},\"Attributes\":[],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs\",\"Position\":{\"Item1\":24,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":32}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"angle\"]},\"Type\":{\"Case\":\"Double\"},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":34},\"Item2\":{\"Line\":1,\"Column\":39}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"Double\"},\"ReturnType\":{\"Case\":\"Int\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[\" # Summary\",\" Rotates a qubit (starting in the |0> state) around the Y axis of the\",\" Bloch Sphere by the given angle, measures it, and returns the result.\",\"\",\" # Input\",\" ## angle\",\" The angle (in radians) to rotate the qubit by. This angle should be\",\" measured from the +Z axis, towards the +X axis.\",\"\",\" # Output\",\" 0 if the qubit was measured in the |0> state, 1 if the qubit was\",\" measured in the |1> state.\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.ConsoleSandbox\",\"Name\":\"RotateAndMeasureQubit\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs\",\"Position\":{\"Item1\":24,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":32}},\"Documentation\":[]}")]
#line hidden
namespace QSharpExercises.ConsoleSandbox
{
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs", OperationFunctor.Body, 25, -1)]
    public partial class RotateAndMeasureQubit : Operation<Double, Int64>, ICallable
    {
        public RotateAndMeasureQubit(IOperationFactory m) : base(m)
        {
        }

        String ICallable.Name => "RotateAndMeasureQubit";
        String ICallable.FullName => "QSharpExercises.ConsoleSandbox.RotateAndMeasureQubit";
        protected Allocate Allocate__
        {
            get;
            set;
        }

        protected Release Release__
        {
            get;
            set;
        }

        protected IUnitary<(Double,Qubit)> Microsoft__Quantum__Intrinsic__Ry
        {
            get;
            set;
        }

        protected ICallable<Qubit, Result> Microsoft__Quantum__Intrinsic__M
        {
            get;
            set;
        }

        protected ICallable<Qubit, QVoid> Reset__
        {
            get;
            set;
        }

        public override Func<Double, Int64> __Body__ => (__in__) =>
        {
            var angle = __in__;
#line hidden
            {
#line 26 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs"
                var qubit = Allocate__.Apply();
#line hidden
                bool __arg1__ = true;
                try
                {
#line 27 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs"
                    Microsoft__Quantum__Intrinsic__Ry.Apply((angle, qubit));
#line 28 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs"
                    var result = Microsoft__Quantum__Intrinsic__M.Apply(qubit);
#line 29 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs"
                    var resultInt = ((result == Result.One) ? 1L : 0L);
#line 31 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs"
                    Reset__.Apply(qubit);
#line 32 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction to Quantum Software Development/exercises/ConsoleSandbox/QuantumCode.qs"
                    return resultInt;
                }
#line hidden
                catch
                {
                    __arg1__ = false;
                    throw;
                }
#line hidden
                finally
                {
                    if (__arg1__)
                    {
#line hidden
                        Release__.Apply(qubit);
                    }
                }
            }
        }

        ;
        public override void __Init__()
        {
            this.Allocate__ = this.__Factory__.Get<Allocate>(typeof(global::Microsoft.Quantum.Intrinsic.Allocate));
            this.Release__ = this.__Factory__.Get<Release>(typeof(global::Microsoft.Quantum.Intrinsic.Release));
            this.Microsoft__Quantum__Intrinsic__Ry = this.__Factory__.Get<IUnitary<(Double,Qubit)>>(typeof(global::Microsoft.Quantum.Intrinsic.Ry));
            this.Microsoft__Quantum__Intrinsic__M = this.__Factory__.Get<ICallable<Qubit, Result>>(typeof(global::Microsoft.Quantum.Intrinsic.M));
            this.Reset__ = this.__Factory__.Get<ICallable<Qubit, QVoid>>(typeof(global::Microsoft.Quantum.Intrinsic.Reset));
        }

        public override IApplyData __DataIn__(Double data) => new QTuple<Double>(data);
        public override IApplyData __DataOut__(Int64 data) => new QTuple<Int64>(data);
        public static System.Threading.Tasks.Task<Int64> Run(IOperationFactory __m__, Double angle)
        {
            return __m__.Run<RotateAndMeasureQubit, Double, Int64>(angle);
        }
    }
}
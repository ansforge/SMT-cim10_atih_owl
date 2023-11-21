package fr.gouv.esante.smt.owl;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.transform.sax.SAXSource;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.RDFXMLDocumentFormat;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.AddOntologyAnnotation;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyID;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.SetOntologyID;
import org.semanticweb.owlapi.vocab.OWL2Datatype;
import org.semanticweb.owlapi.vocab.PROVVocabulary;
import org.semanticweb.owlapi.vocab.SKOSVocabulary;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;

import ca.uhn.fhir.parser.DataFormatException;
import fr.gouv.esante.smt.claml.models.Cell;
import fr.gouv.esante.smt.claml.models.ClaML;
import fr.gouv.esante.smt.claml.models.Class;
import fr.gouv.esante.smt.claml.models.ClassKind;
import fr.gouv.esante.smt.claml.models.ExcludeModifier;
import fr.gouv.esante.smt.claml.models.Fragment;
import fr.gouv.esante.smt.claml.models.Label;
import fr.gouv.esante.smt.claml.models.ListItem;
import fr.gouv.esante.smt.claml.models.Meta;
import fr.gouv.esante.smt.claml.models.ModifiedBy;
import fr.gouv.esante.smt.claml.models.Modifier;
import fr.gouv.esante.smt.claml.models.ModifierClass;
import fr.gouv.esante.smt.claml.models.Para;
import fr.gouv.esante.smt.claml.models.Reference;
import fr.gouv.esante.smt.claml.models.Row;
import fr.gouv.esante.smt.claml.models.Rubric;
import fr.gouv.esante.smt.claml.models.RubricKind;
import fr.gouv.esante.smt.claml.models.SubClass;
import fr.gouv.esante.smt.claml.models.SuperClass;
import fr.gouv.esante.smt.claml.models.TBody;
import fr.gouv.esante.smt.claml.models.Table;
import fr.gouv.esante.smt.claml.models.Term;
import fr.gouv.esante.smt.claml.models.UsageKind;
import fr.gouv.esante.smt.utils.ATIHCIM10Vocabulary;
import fr.gouv.esante.smt.utils.DCTVocabulary;
import fr.gouv.esante.smt.utils.DCVocabulary;
import fr.gouv.esante.smt.utils.PropertiesUtil;
import fr.gouv.esante.smt.utils.SkosVocabulary;
import fr.gouv.esante.smt.utils.XSkosVocabulary;
import uk.ac.manchester.cs.owl.owlapi.OWLAnnotationPropertyImpl;

public class ClamOwlTransformer {

	private static final Logger log = LoggerFactory.getLogger(ClamOwlTransformer.class);
	private static OWLOntologyManager manager;
	private static OWLOntology onto;
	private static OWLDataFactory fact;
	private static ClaML claml;
	private static Map<String, Modifier> modifierMap = null;
	private static Map<String, ModifierClass> modifierClassMap = null;
	private static Map<String, Class> classMap = null;
	private static OWLAnnotationProperty classKind = null;
	private static OWLAnnotationProperty classCode = null;
	private static Writer csvWriter = null;
	private static List<String> listItemIncl = null;
	private static List<String> listItemExcl = null;
	private static String niveauList = "";
	private static Integer niveauListHTML = 0;
	private static Integer niveauListHTMLInclA = 0;
	private static Integer niveauListHTMLInclP = 0;
	private static boolean niveauListHTMLIncl1P = false;
	private static boolean niveauListHTMLIncl2P = false;
	private static boolean niveauListHTMLIncl3P = false;
	private static boolean firdtListInclElm = false;
	private static boolean firstListInclElmText = false;
	
	private static Integer niveauListHTMLExclA = 0;
	private static Integer niveauListHTMLExclP = 0;
	private static boolean niveauListHTMLExcl1P = false;
	private static boolean niveauListHTMLExcl2P = false;
	private static boolean niveauListHTMLExcl3P = false;
	private static boolean niveauListHTMLExcl4P = false;
	private static boolean firstListExclElm = false;
	private static boolean firstListExclElmText = false;
	
	private static boolean htmlNote = false;
	
	private static List<String> listItemHTMLIncl = null;
	private static List<String> listItemHTMLExcl = null;
	private static Map<String, List<String>> mapCodeInclDagger = null;
	private static Map<String, List<String>> mapCodeInclAster = null;
	private static List<String> cimReferences = Arrays.asList("N00.9","N03.9","F10.0","V26","F17.2","F10.0","F10.2","F10.5","F10.4","F10.6");
	
	private static String cim10OWLFile = PropertiesUtil.getProperties("cim10OWLFile");
	private static String cim10ClamlFile = PropertiesUtil.getProperties("cim10ClamlFile");


	public static void main(final String[] args) throws Exception {
		
		//System.setProperty("file.encoding","UTF-8" );

		csvWriter = new OutputStreamWriter(new FileOutputStream(PropertiesUtil.getProperties("clamlIgnoredCode")), StandardCharsets.UTF_8);

		//File cimClaML = new File(PropertiesUtil.getProperties("cim10ClamlFile"));
		final File cimClaML = new File(cim10ClamlFile);

		//OutputStream cimOWL = new FileOutputStream(PropertiesUtil.getProperties("cim10OWLFile"));
		final OutputStream cimOWL = new FileOutputStream(cim10OWLFile);
		manager = OWLManager.createOWLOntologyManager();
		log.info("creation ontologie structure");
		onto = manager.createOntology();
		log.info("ajout ontologie IRI");
		IRI cimIRI = IRI.create("http://data.esante.gouv.fr/atih/cim10#");
		manager.applyChange(new SetOntologyID(onto, new OWLOntologyID(cimIRI)));
		fact = onto.getOWLOntologyManager().getOWLDataFactory();
		
		
		claml2owl(cimClaML, cimOWL);

		csvWriter.flush();
	    csvWriter.close();

	}

	static void claml2owl(File clamlFile, OutputStream output)
			throws DataFormatException, IOException, ParserConfigurationException, SAXException {

		try {
			JAXBContext jaxbContext = JAXBContext.newInstance(ClaML.class);

			SAXParserFactory spf = SAXParserFactory.newInstance();
			spf.setFeature("http://apache.org/xml/features/nonvalidating/load-external-dtd", false);
			spf.setFeature("http://xml.org/sax/features/validation", false);

			XMLReader xmlReader = spf.newSAXParser().getXMLReader();
			
			InputStream inputStream = new FileInputStream(clamlFile);
			Reader reader = new InputStreamReader(inputStream, "UTF-8");
			InputSource inputSource = new InputSource(reader);
			
			
			//InputSource inputSource = new InputSource(new FileReader(clamlFile));
		//	inputSource.setEncoding(StandardCharsets.UTF_8.displayName());
			SAXSource source = new SAXSource(xmlReader, inputSource);

			Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
			claml = (ClaML) jaxbUnmarshaller.unmarshal(source);

			modifierMap = new HashMap<String, Modifier>();
			modifierClassMap = new HashMap<String, ModifierClass>();
			classMap = new HashMap<String, Class>();

			for (Modifier m : claml.getModifier()) {
				modifierMap.put(m.getCode(), m);
			}

			for (ModifierClass mc : claml.getModifierClass()) {
				modifierClassMap.put(mc.getModifier() + mc.getCode(), mc);
			}

			for (Class c : claml.getClazz()) {
				classMap.put(c.getCode(), c);
			}

			for (Class c : claml.getClazz()) {
				addClass(c);
			}
			log.info("creation class code");
			for (Class c : claml.getClazz()) {
				appliquerModifier(c);
			}
			log.info("ajout ontologie metadonnées");
			for (Meta meta : claml.getMeta()) {
				if (meta.getName().equals("copyright")) {
					OWLAnnotationProperty dctrights = fact.getOWLAnnotationProperty(DCTVocabulary.rights.getIRI());
					OWLAnnotation annotrights = fact.getOWLAnnotation(dctrights, fact.getOWLLiteral(meta.getValue()));
					manager.applyChange(new AddOntologyAnnotation(onto, annotrights));
				}
			}
			
			OWLAnnotationProperty publisher = fact.getOWLAnnotationProperty(DCTVocabulary.publisher.getIRI());
			OWLAnnotation annotpublisher = fact.getOWLAnnotation(publisher, IRI.create("https://esante.gouv.fr/"));
			manager.applyChange(new AddOntologyAnnotation(onto, annotpublisher));
			
			OWLAnnotationProperty dctcreator = fact.getOWLAnnotationProperty(DCTVocabulary.creator.getIRI());
			OWLAnnotation annotcreator = fact.getOWLAnnotation(dctcreator, IRI.create("https://www.atih.sante.fr/"));
			manager.applyChange(new AddOntologyAnnotation(onto, annotcreator));
			
			OWLAnnotationProperty dctsource = fact.getOWLAnnotationProperty(DCTVocabulary.source.getIRI());
			OWLAnnotation annotsource = fact.getOWLAnnotation(dctsource, IRI.create("https://www.atih.sante.fr/sites/default/files/public/content/3963/cim10frfm2021syst_claml_20210330_0.zip"));
			manager.applyChange(new AddOntologyAnnotation(onto, annotsource));

			RDFXMLDocumentFormat ontologyFormat = new RDFXMLDocumentFormat();
			ontologyFormat.setPrefix("icd", "http://id.who.int/icd/schema/");
			ontologyFormat.setPrefix("dct", "http://purl.org/dc/terms/");

			OWLAnnotation annot = fact.getOWLAnnotation(fact.getRDFSLabel(),
					fact.getOWLLiteral(claml.getTitle().getContent(), "fr"));
			manager.applyChange(new AddOntologyAnnotation(onto, annot));
			
			OWLClass owlClass = null;
			String about = "http://data.esante.gouv.fr/atih/cim10";
			owlClass = fact.getOWLClass(IRI.create(about));
			OWLAxiom declare = fact.getOWLDeclarationAxiom(owlClass);
			manager.applyChange(new AddAxiom(onto, declare));
			
			OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
			manager.applyChange(new AddAxiom(onto, axiom));
			

			OWLAnnotationProperty dctIssued = fact.getOWLAnnotationProperty(DCTVocabulary.issued.getIRI());
			OWLAnnotation annotIssued = fact.getOWLAnnotation(dctIssued,
					fact.getOWLLiteral(claml.getTitle().getDate() + "T00:00:00", OWL2Datatype.XSD_DATE_TIME));
			manager.applyChange(new AddOntologyAnnotation(onto, annotIssued));

			OWLAnnotation annotVersion = fact.getOWLAnnotation(fact.getOWLVersionInfo(),
					fact.getOWLLiteral(claml.getTitle().getVersion()));
			manager.applyChange(new AddOntologyAnnotation(onto, annotVersion));

			manager.saveOntology(onto, ontologyFormat, output);

		} catch (JAXBException | OWLOntologyStorageException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	static void addClass(Class clazz) throws IOException {
		OWLClass owlClass = null;
		String about = "http://data.esante.gouv.fr/atih/cim10/" + clazz.getCode();
		owlClass = fact.getOWLClass(IRI.create(about));
		OWLAxiom declare = fact.getOWLDeclarationAxiom(owlClass);
		manager.applyChange(new AddAxiom(onto, declare));
		addClassKind(owlClass, getClassKindName(clazz.getKind()));
		addClassCode(owlClass, clazz.getCode());
		
		if(getClassKindName(clazz.getKind()).equals("chapter")) {
			String broderUri = "http://data.esante.gouv.fr/atih/cim10";
			OWLSubClassOfAxiom ax1 = fact.getOWLSubClassOfAxiom(owlClass, fact.getOWLClass(IRI.create(broderUri)));
			manager.applyChange(new AddAxiom(onto, ax1));
		}

		for (SuperClass sup : clazz.getSuperClass()) {
			if (sup.getCode().equals("N01") || sup.getCode().equals("N02") || sup.getCode().equals("N03")
					|| sup.getCode().equals("N04")) {
				addClassParent(owlClass, clazz.getCode().substring(0, clazz.getCode().length() - 1));
			} else {
				addClassParent(owlClass, sup.getCode());
				if(clazz.getCode().endsWith(".9")) {
					addSupClassExclusion(owlClass, sup.getCode());
				}
			}
		}

//		for (SubClass sub : clazz.getSubClass()) {
//			addClassChild(owlClass, sub);
//		}

		for (Meta meta : clazz.getMeta()) {
			if (meta.getName().equals("frenchspecific")) {
				addClassMetaCreator(owlClass, meta);
			}
		}
		String note = "";
		String incl = "";
		String excl = "";
		String inclHtml = "";
		String exclHtml = "";
		listItemIncl = new ArrayList<>();
		listItemExcl = new ArrayList<>();
		listItemHTMLIncl = new ArrayList<>();
		listItemHTMLExcl = new ArrayList<>();
		mapCodeInclDagger = new HashMap<String, List<String>>();
		mapCodeInclAster = new HashMap<String, List<String>>();
		niveauListHTMLInclA = 0;
		niveauListHTMLIncl1P = false;
		niveauListHTMLIncl2P = false;
		niveauListHTMLIncl3P = false;
		firdtListInclElm = false;
		firstListInclElmText = false;
		
		niveauListHTMLExclA = 0;
		niveauListHTMLExcl1P = false;
		niveauListHTMLExcl2P = false;
		niveauListHTMLExcl3P = false;
		firstListExclElm = false;
		firstListExclElmText = false;
		
		htmlNote = false;
		for (Rubric rubric : clazz.getRubric()) {
			Object kind = rubric.getKind();
			RubricKind rkind = (RubricKind) kind;
			if (rkind.getName().equals("preferred")) {
				String value = getLabelValueWithoutReference(rubric.getLabel().get(0));
				addClassLabel(owlClass, value);
				if (!getReferenceUsageValue(rubric.getLabel().get(0)).isEmpty()) {
					for (String ss : getReferenceUsageValue(rubric.getLabel().get(0)).split(",")) {
						if (!ss.isEmpty() && ss.split(":").length == 2) {
							String code = ss.split(":")[0];
							String sym = ss.split(":")[1];
							if (sym.equals("dagger")) {
								addClassUsageDagger(owlClass, code);
							} else if (sym.equals("aster")) {
								addClassUsageAster(owlClass, code);
							}
						}
					}
				}
			} else if (rkind.getName().equals("definition")) {
				String value = getLabelValue(rubric.getLabel().get(0));
				addClassComment(owlClass, value);
			} else if (rkind.getName().equals("note")) {
				note += getLabelValue(rubric.getLabel().get(0)) + "\n";
				
			} else if (rkind.getName().equals("coding-hint")) {
				String value = getLabelValue(rubric.getLabel().get(0));
				addClassCodingHint(owlClass, value);
			} else if (rkind.getName().equals("introduction")) {
				String intro = getIntroductionValue(rubric.getLabel().get(0));
				if(intro.contains("<li>")) {
					htmlNote = true;
					note += intro + "\n";
				}else {
					note += intro + "\n";
				}
			}else if (rkind.getName().equals("inclusion")) {
				String value = getAltLabelValue(rubric.getLabel().get(0));
				addClassInclusion(owlClass, value);
				if (!getReferenceUsageValue(rubric.getLabel().get(0)).isEmpty()) {
					for (String ss : getReferenceUsageValue(rubric.getLabel().get(0)).split(",")) {
						if (!ss.isEmpty() && ss.split(":").length == 2) {
							String code = ss.split(":")[0];
							String sym = ss.split(":")[1];
							if (sym.equals("dagger")) {
								if(mapCodeInclDagger.containsKey(code)) {
									List<String> valueList = mapCodeInclDagger.get(code);
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclDagger.put(code, valueList);
								}else {
									List<String> valueList = new ArrayList<String>();
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclDagger.put(code, valueList);
								}
								
							} else if (sym.equals("aster")) {
								if(mapCodeInclAster.containsKey(code)) {
									List<String> valueList = mapCodeInclAster.get(code);
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclAster.put(code, valueList);
								}else {
									List<String> valueList = new ArrayList<String>();
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclAster.put(code, valueList);
								}
								
							}
						}
					}
				}
				niveauList = "";
				niveauListHTML = 0;
				niveauListHTMLInclP = 0;
				String val = getHTMLInclLabelValue(rubric.getLabel().get(0)) + "\n";
				if(!firdtListInclElm) {
					val = "<li>" + val.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "</li> \n";
				}
				inclHtml += val;
				String valText = getInclExclValue(rubric.getLabel().get(0)).replace("\n\t\t\t\t", "").replace("\n\t\t\t", "")+ "\n";
				if(!firstListInclElmText) {
					valText = valText.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "\n";
				}
				incl += valText;
			} else if (rkind.getName().equals("exclusion")) {
				niveauList = "";
				niveauListHTML = 0;
				niveauListHTMLExclP = 0;
				String val = getHTMLExclLabelValue(rubric.getLabel().get(0)) + "\n";
				if(!firstListExclElm) {
					val = "<li>" + val.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "</li> \n";
				}
				exclHtml += val;
				
				String valText = getExclExclValue(rubric.getLabel().get(0)).replace("\n\t\t\t\t", "").replace("\n\t\t\t", "")+ "\n";
				if(!firstListExclElmText) {
					valText = valText.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "\n";
				}
				excl += valText;
				
				String referenceValue = getReferenceValue(rubric.getLabel().get(0));
				if (!referenceValue.trim().isEmpty()) {
					addClassDisjointExclusion(owlClass, referenceValue.replace(".-", "").replace(".–", ""));
				}
			}
		}
		
		if(!mapCodeInclDagger.isEmpty()) {
			addClassUsageDagger(owlClass, mapCodeInclDagger);
		}
		
		if(!mapCodeInclAster.isEmpty()) {
			addClassUsageAster(owlClass, mapCodeInclAster);
		}

		if (note.length() > 0) {
			if(htmlNote) {
				addClassHtmlNote(owlClass, "<ul>" +note + "</ul>");
			}else {
				addClassNote(owlClass, note);
			}
		}
		if (inclHtml.length() > 0) {
			String val = "<ul>" + inclHtml;
			if(niveauListHTMLInclA == 0) {
				val += "</ul>";
			}else {
				if(niveauListHTMLIncl3P && niveauListHTMLInclA == 3) {
					val += "</ul>";
				}
				if(niveauListHTMLIncl2P) {
					val += "</li> \n </ul> \n </li>";
				}
				if(niveauListHTMLIncl1P && !niveauListHTMLIncl2P){
					val += "</ul> \n </li>";
				}
				val += "</ul>";
			}
			
//			addClassHtmlInclusion(owlClass, val);
			addClassXInclusion(owlClass, incl.replace("\n\t\t\t\t\n\t\t\t\t\n\t\t\t", "").replace("\t\t\t\n\t\t\t\t\n", ""));
		}
		if (exclHtml.length() > 0) {
			String val = "<ul>" + exclHtml;
			if(niveauListHTMLExclA == 0) {
				val += "</ul>";
			}else {
				if(niveauListHTMLExcl3P && niveauListHTMLExclA == 3) {
					val += "</li> \n </ul>";
				}
				if(niveauListHTMLExcl2P) {
					val += "</li> \n </ul> \n </li>";
				}
				if(niveauListHTMLExcl1P && !niveauListHTMLExcl2P){
					val += "</ul> \n </li>";
				}
				val += "</ul>";
			}
//			addClassHtmlExclusion(owlClass, val);
			addClassExclusion(owlClass, excl.replace("\n\t\t\t\t\n\t\t\t\t\n\t\t\t", "").replace("\t\t\t\n\t\t\t\t\n", ""));
		}
		
		for(ModifiedBy m : clazz.getModifiedBy()) {
			String mdNote = "";
			Modifier md = modifierMap.get(m.getCode());
			for (Rubric rubric : md.getRubric()) {
				Object kind = rubric.getKind();
				RubricKind rkind = (RubricKind) kind;
				if (rkind.getName().equals("text")) {
					mdNote += getLabelValue(rubric.getLabel().get(0)) + "\n";
				}
			}
			
			for (SubClass mc : md.getSubClass()) {
				ModifierClass mdc = modifierClassMap.get(md.getCode() + mc.getCode());
				
				for (Rubric rubric : mdc.getRubric()) {
					Object kind = rubric.getKind();
					RubricKind rkind = (RubricKind) kind;
					if (rkind.getName().equals("preferred")) {
						mdNote += mdc.getCode() + "    " + getLabelValue(rubric.getLabel().get(0)) + "\n";
					}
				}
			}
			if (mdNote.length() > 0) {
				addClassNote(owlClass, mdNote);
			}
		}

	}

	private static void appliquerModifier(Class clazz) throws IOException {
		if (clazz.getSuperClass().isEmpty()
				|| classMap.get(clazz.getSuperClass().get(0).getCode()).getModifiedBy().isEmpty()) {
			Integer numbModifier = clazz.getModifiedBy().size();
			if (numbModifier > 0) {
				if (clazz.getSubClass().isEmpty() || clazz.getCode().equals("N01") || clazz.getCode().equals("N02")
						|| clazz.getCode().equals("N03") || clazz.getCode().equals("N04")) {
					if (numbModifier == 1) {
						Modifier md = modifierMap.get(clazz.getModifiedBy().get(0).getCode());
						for (SubClass mc : md.getSubClass()) {
							ModifierClass mdc = modifierClassMap.get(md.getCode() + mc.getCode());
							appliquerModifierClass(clazz, mdc);
						}
					} else if (numbModifier == 2) {
						Modifier md1 = modifierMap.get(clazz.getModifiedBy().get(0).getCode());
						Modifier md2 = modifierMap.get(clazz.getModifiedBy().get(1).getCode());
						for (SubClass mc1 : md1.getSubClass()) {
							ModifierClass mdc1 = modifierClassMap.get(md1.getCode() + mc1.getCode());
							appliquerModifierClass(clazz, mdc1);
							for (SubClass mc2 : md2.getSubClass()) {
								ModifierClass mdc2 = modifierClassMap.get(md2.getCode() + mc2.getCode());
								appliquerModifierClass(clazz, mdc1, mdc2);
							}
						}
					}
				} else {
					if (numbModifier == 1) {
						for (SubClass sc : clazz.getSubClass()) {
							Class subClazz = classMap.get(sc.getCode());
							boolean excluded = false;
							for (ExcludeModifier em : subClazz.getExcludeModifier()) {
								if (em.getCode().equals(clazz.getModifiedBy().get(0).getCode())) {
									excluded = true;
								}
							}
							if (!excluded) {
								Modifier md = modifierMap.get(clazz.getModifiedBy().get(0).getCode());
								for (SubClass mc : md.getSubClass()) {
									ModifierClass mdc = modifierClassMap.get(md.getCode() + mc.getCode());
									appliquerModifierClass(subClazz, mdc);
									if (!subClazz.getModifiedBy().isEmpty()) {
										Modifier md2 = modifierMap.get(subClazz.getModifiedBy().get(0).getCode());
										if (!md.getCode().equals(md2.getCode())) {
											for (SubClass mc2 : md2.getSubClass()) {
												ModifierClass mdc2 = modifierClassMap
														.get(md2.getCode() + mc2.getCode());
												appliquerModifierClass(subClazz, mdc, mdc2);
											}
										}
									}
								}
							}

						}

					} else if (numbModifier == 2) {
						for (SubClass sc : clazz.getSubClass()) {
							Class subClazz = classMap.get(sc.getCode());
							boolean excluded1 = false;
							boolean excluded2 = false;
							for (ExcludeModifier em : subClazz.getExcludeModifier()) {
								if (em.getCode().equals(clazz.getModifiedBy().get(0).getCode())) {
									excluded1 = true;
								}
								if (em.getCode().equals(clazz.getModifiedBy().get(1).getCode())) {
									excluded2 = true;
								}
							}
							if (!excluded1) {
								Modifier md1 = modifierMap.get(clazz.getModifiedBy().get(0).getCode());
								Modifier md2 = modifierMap.get(clazz.getModifiedBy().get(1).getCode());
								for (SubClass mc1 : md1.getSubClass()) {
									ModifierClass mdc1 = modifierClassMap.get(md1.getCode() + mc1.getCode());
									appliquerModifierClass(subClazz, mdc1);
									if (!excluded2) {
										for (SubClass mc2 : md2.getSubClass()) {
											ModifierClass mdc2 = modifierClassMap.get(md2.getCode() + mc2.getCode());
											appliquerModifierClass(subClazz, mdc1, mdc2);
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}

	private static void appliquerModifierClass(Class clazz, ModifierClass mdc) throws IOException {
		OWLClass owlSubClass = null;
		String subAbout = "http://data.esante.gouv.fr/atih/cim10/" + clazz.getCode() + mdc.getCode();
		owlSubClass = fact.getOWLClass(IRI.create(subAbout));
		OWLAxiom subDeclare = fact.getOWLDeclarationAxiom(owlSubClass);
		manager.applyChange(new AddAxiom(onto, subDeclare));
		addClassCode(owlSubClass, clazz.getCode() + mdc.getCode());

		OWLSubClassOfAxiom ax1 = fact.getOWLSubClassOfAxiom(owlSubClass,
				fact.getOWLClass(IRI.create("http://data.esante.gouv.fr/atih/cim10/" + clazz.getCode())));
		manager.applyChange(new AddAxiom(onto, ax1));

		String supValue = "";
		String subValue = "";
		for (Rubric rubric : clazz.getRubric()) {
			Object kind = rubric.getKind();
			RubricKind rkind = (RubricKind) kind;
			if (rkind.getName().equals("preferred")) {
				supValue = getLabelValue(rubric.getLabel().get(0));
				if (!getReferenceUsageValue(rubric.getLabel().get(0)).isEmpty()) {
					for (String ss : getReferenceUsageValue(rubric.getLabel().get(0)).split(",")) {
						if (!ss.isEmpty() && ss.split(":").length == 2) {
							String code = ss.split(":")[0];
							String sym = ss.split(":")[1];
							if (sym.equals("dagger")) {
								addClassUsageDagger(owlSubClass, code);
							} else if (sym.equals("aster")) {
								addClassUsageAster(owlSubClass, code);
							}
						}
					}
				}
			}else if (rkind.getName().equals("inclusion")) {
				String value = getAltLabelValue(rubric.getLabel().get(0));
				if (!getReferenceUsageValue(rubric.getLabel().get(0)).isEmpty()) {
					for (String ss : getReferenceUsageValue(rubric.getLabel().get(0)).split(",")) {
						if (!ss.isEmpty() && ss.split(":").length == 2) {
							String code = ss.split(":")[0];
							String sym = ss.split(":")[1];
							if (sym.equals("dagger")) {
								if(mapCodeInclDagger.containsKey(code)) {
									List<String> valueList = mapCodeInclDagger.get(code);
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclDagger.put(code, valueList);
								}else {
									List<String> valueList = new ArrayList<String>();
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclDagger.put(code, valueList);
								}
								
							} else if (sym.equals("aster")) {
								if(mapCodeInclAster.containsKey(code)) {
									List<String> valueList = mapCodeInclAster.get(code);
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclAster.put(code, valueList);
								}else {
									List<String> valueList = new ArrayList<String>();
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclAster.put(code, valueList);
								}
								
							}
						}
					}
				}
			}
		}
		
		if(!mapCodeInclDagger.isEmpty()) {
			addClassUsageDagger(owlSubClass, mapCodeInclDagger);
		}
		
		if(!mapCodeInclAster.isEmpty()) {
			addClassUsageAster(owlSubClass, mapCodeInclAster);
		}

		String incl = "";
		String excl = "";
		String inclHtml = "";
		String exclHtml = "";
		
		listItemIncl = new ArrayList<>();
		listItemExcl = new ArrayList<>();
		listItemHTMLIncl = new ArrayList<>();
		listItemHTMLExcl = new ArrayList<>();
		mapCodeInclDagger = new HashMap<String, List<String>>();
		mapCodeInclAster = new HashMap<String, List<String>>();
		niveauListHTMLInclA = 0;
		niveauListHTMLIncl1P = false;
		niveauListHTMLIncl2P = false;
		niveauListHTMLIncl3P = false;
		firdtListInclElm = false;
		firstListInclElmText = false;
		
		niveauListHTMLExclA = 0;
		niveauListHTMLExcl1P = false;
		niveauListHTMLExcl2P = false;
		niveauListHTMLExcl3P = false;
		firstListExclElm = false;
		firstListExclElmText = false;
		String specialModifier = "";
		for (Rubric rubric : mdc.getRubric()) {
			Object kind = rubric.getKind();
			RubricKind rkind = (RubricKind) kind;
			if (rkind.getName().equals("preferred")) {
				subValue = getLabelValue(rubric.getLabel().get(0));
			} else if (rkind.getName().equals("inclusion")) {
				String value = getAltLabelValue(rubric.getLabel().get(0));
				addClassInclusion(owlSubClass, value);
				
				niveauList = "";
				niveauListHTML = 0;
				niveauListHTMLInclP = 0;
				String val = getHTMLInclLabelValue(rubric.getLabel().get(0)) + "\n";
				if(!firdtListInclElm) {
					val = "<li>" + val.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "</li> \n";
				}
				inclHtml += val;
				String valText = getInclExclValue(rubric.getLabel().get(0)).replace("\n\t\t\t\t", "").replace("\n\t\t\t", "")+ "\n";
				if(!firstListInclElmText) {
					valText = valText.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "\n";
				}
				incl += valText;
				
			} else if (rkind.getName().equals("definition")) {
				String value = getDefValue(rubric.getLabel().get(0));
				if (!value.contains("#")) {
					addClassComment(owlSubClass, value);
				} else {
					specialModifier = value.replace("\n", "£").replaceAll("\t+", "").trim();
				}
			}else if (rkind.getName().equals("exclusion")) {
				niveauList = "";
				niveauListHTML = 0;
				niveauListHTMLExclP = 0;
				String val = getHTMLExclLabelValue(rubric.getLabel().get(0)) + "\n";
				if(!firstListExclElm) {
					val = "<li>" + val.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "</li> \n";
				}
				exclHtml += val;
				String valText = getExclExclValue(rubric.getLabel().get(0)).replace("\n\t\t\t\t", "").replace("\n\t\t\t", "")+ "\n";
				if(!firstListExclElmText) {
					valText = valText.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "\n";
				}
				excl += valText;
				
			
			}
		}
		
		if (inclHtml.length() > 0) {
			String val = "<ul>" + inclHtml;
			if(niveauListHTMLInclA == 0) {
				val += "</ul>";
			}else {
				if(niveauListHTMLIncl3P && niveauListHTMLInclA == 3) {
					val += "</ul>";
				}
				if(niveauListHTMLIncl2P) {
					val += "</li> \n </ul> \n </li>";
				}
				if(niveauListHTMLIncl1P && !niveauListHTMLIncl2P){
					val += "</ul> \n </li>";
				}
				val += "</ul>";
			}
			
//			addClassHtmlInclusion(owlSubClass, val);
			addClassXInclusion(owlSubClass, incl.replace("\n\t\t\t\t\n\t\t\t\t\n\t\t\t", "").replace("\t\t\t\n\t\t\t\t\n", ""));
		}
		if (exclHtml.length() > 0) {
			String val = "<ul>" + exclHtml;
			if(niveauListHTMLExclA == 0) {
				val += "</ul>";
			}else {
				if(niveauListHTMLExcl3P && niveauListHTMLExclA == 3) {
					val += "</li> \n </ul>";
				}
				if(niveauListHTMLExcl2P) {
					val += "</li> \n </ul> \n </li>";
				}
				if(niveauListHTMLExcl1P && !niveauListHTMLExcl2P){
					val += "</ul> \n </li>";
				}
				val += "</ul>";
			}
//			addClassHtmlExclusion(owlSubClass, val);
			addClassExclusion(owlSubClass, excl.replace("\n\t\t\t\t\n\t\t\t\t\n\t\t\t", "").replace("\t\t\t\n\t\t\t\t\n", ""));
		}
		
		AddGeneratedBy(owlSubClass);
		addClassLabel(owlSubClass, supValue + " - \" " + subValue + " \"");
		addClassKind(owlSubClass, "category");

		/*
		 * traitement pour Modifier S05F10_4
		 */
		if (mdc.getModifier().equals("S05F10_4") && !specialModifier.isEmpty()) {
			for (String mm : specialModifier.split("£")) {
				if (!mm.isEmpty()) {
					String[] ref = mm.split("#");
					String code = ref[0];
					String label = ref[1];
					OWLClass owlSubClass2 = null;
					String subAbout2 = "http://data.esante.gouv.fr/atih/cim10/" + clazz.getCode() + mdc.getCode()
							+ code;
					owlSubClass2 = fact.getOWLClass(IRI.create(subAbout2));
					OWLAxiom subDeclare2 = fact.getOWLDeclarationAxiom(owlSubClass2);
					manager.applyChange(new AddAxiom(onto, subDeclare2));
					addClassCode(owlSubClass2, clazz.getCode() + mdc.getCode() + code);

					OWLSubClassOfAxiom ax2 = fact.getOWLSubClassOfAxiom(owlSubClass2,
							fact.getOWLClass(IRI.create(subAbout2.substring(0, subAbout2.length() - 1))));
					manager.applyChange(new AddAxiom(onto, ax2));
					if (inclHtml.length() > 0) {
						String val = "<ul>" + inclHtml;
						if(niveauListHTMLInclA == 0) {
							val += "</ul>";
						}else {
							if(niveauListHTMLIncl3P && niveauListHTMLInclA == 3) {
								val += "</ul>";
							}
							if(niveauListHTMLIncl2P) {
								val += "</li> \n </ul> \n </li>";
							}
							if(niveauListHTMLIncl1P && !niveauListHTMLIncl2P){
								val += "</ul> \n </li>";
							}
							val += "</ul>";
						}
//						addClassHtmlInclusion(owlSubClass2, val);
						addClassXInclusion(owlSubClass2, incl.replace("\n\t\t\t\t\n\t\t\t\t\n\t\t\t", "").replace("\t\t\t\n\t\t\t\t\n", ""));
					}
					
					AddGeneratedBy(owlSubClass2);
					addClassLabel(owlSubClass2, supValue + " - \"" + subValue + "\"" + " - \"" + label + "\"");
					addClassKind(owlSubClass2, "category");
				}
			}
		}
	}

	private static void appliquerModifierClass(Class clazz, ModifierClass mdc1, ModifierClass mdc2) {
		OWLClass owlSubClass = null;
		String subAbout = "http://data.esante.gouv.fr/atih/cim10/" + clazz.getCode() + mdc1.getCode() + mdc2.getCode();
		owlSubClass = fact.getOWLClass(IRI.create(subAbout));
		OWLAxiom subDeclare = fact.getOWLDeclarationAxiom(owlSubClass);
		manager.applyChange(new AddAxiom(onto, subDeclare));
		addClassCode(owlSubClass, clazz.getCode() + mdc1.getCode() + mdc2.getCode());

		OWLSubClassOfAxiom ax = fact.getOWLSubClassOfAxiom(owlSubClass, fact
				.getOWLClass(IRI.create("http://data.esante.gouv.fr/atih/cim10/" + clazz.getCode() + mdc1.getCode())));
		manager.applyChange(new AddAxiom(onto, ax));
		String subValue2 = "";
		String supValue = "";
		String subValue1 = "";
		for (Rubric rubric : clazz.getRubric()) {
			Object kind = rubric.getKind();
			RubricKind rkind = (RubricKind) kind;
			if (rkind.getName().equals("preferred")) {
				supValue = getLabelValue(rubric.getLabel().get(0));
				if (!getReferenceUsageValue(rubric.getLabel().get(0)).isEmpty()) {
					for (String ss : getReferenceUsageValue(rubric.getLabel().get(0)).split(",")) {
						if (!ss.isEmpty() && ss.split(":").length == 2) {
							String code = ss.split(":")[0];
							String sym = ss.split(":")[1];
							if (sym.equals("dagger")) {
								addClassUsageDagger(owlSubClass, code);
							} else if (sym.equals("aster")) {
								addClassUsageAster(owlSubClass, code);
							}
						}
					}
				}
			}else if (rkind.getName().equals("inclusion")) {
				String value = getAltLabelValue(rubric.getLabel().get(0));
				if (!getReferenceUsageValue(rubric.getLabel().get(0)).isEmpty()) {
					for (String ss : getReferenceUsageValue(rubric.getLabel().get(0)).split(",")) {
						if (!ss.isEmpty() && ss.split(":").length == 2) {
							String code = ss.split(":")[0];
							String sym = ss.split(":")[1];
							if (sym.equals("dagger")) {
								if(mapCodeInclDagger.containsKey(code)) {
									List<String> valueList = mapCodeInclDagger.get(code);
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclDagger.put(code, valueList);
								}else {
									List<String> valueList = new ArrayList<String>();
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclDagger.put(code, valueList);
								}
								
							} else if (sym.equals("aster")) {
								if(mapCodeInclAster.containsKey(code)) {
									List<String> valueList = mapCodeInclAster.get(code);
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclAster.put(code, valueList);
								}else {
									List<String> valueList = new ArrayList<String>();
									valueList.add(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim());
									mapCodeInclAster.put(code, valueList);
								}
								
							}
						}
					}
				}
			}
		}
		
		if(!mapCodeInclDagger.isEmpty()) {
			addClassUsageDagger(owlSubClass, mapCodeInclDagger);
		}
		
		if(!mapCodeInclAster.isEmpty()) {
			addClassUsageAster(owlSubClass, mapCodeInclAster);
		}
		String incl = "";
		String excl = "";
		String inclHtml = "";
		String exclHtml = "";
		
		listItemIncl = new ArrayList<>();
		listItemExcl = new ArrayList<>();
		listItemHTMLIncl = new ArrayList<>();
		listItemHTMLExcl = new ArrayList<>();
		mapCodeInclDagger = new HashMap<String, List<String>>();
		mapCodeInclAster = new HashMap<String, List<String>>();
		niveauListHTMLInclA = 0;
		niveauListHTMLIncl1P = false;
		niveauListHTMLIncl2P = false;
		niveauListHTMLIncl3P = false;
		firdtListInclElm = false;
		firstListInclElmText = false;
		
		niveauListHTMLExclA = 0;
		niveauListHTMLExcl1P = false;
		niveauListHTMLExcl2P = false;
		niveauListHTMLExcl3P = false;
		firstListExclElm = false;
		firstListExclElmText = false;
		for (Rubric rubric : mdc1.getRubric()) {
			Object kind = rubric.getKind();
			RubricKind rkind = (RubricKind) kind;
			if (rkind.getName().equals("preferred")) {
				subValue1 = getLabelValue(rubric.getLabel().get(0));
			} 
		}

		for (Rubric rubric : mdc2.getRubric()) {
			Object kind = rubric.getKind();
			RubricKind rkind = (RubricKind) kind;
			if (rkind.getName().equals("preferred")) {
				subValue2 = getLabelValue(rubric.getLabel().get(0));
			} else if (rkind.getName().equals("inclusion")) {
				String value = getAltLabelValue(rubric.getLabel().get(0));
				addClassInclusion(owlSubClass, value);
				niveauList = "";
				niveauListHTML = 0;
				niveauListHTMLInclP = 0;
				String val = getHTMLInclLabelValue(rubric.getLabel().get(0)) + "\n";
				if(!firdtListInclElm) {
					val = "<li>" + val.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "</li> \n";
				}
				inclHtml += val;
				String valText = getInclExclValue(rubric.getLabel().get(0)).replace("\n\t\t\t\t", "").replace("\n\t\t\t", "")+ "\n";
				if(!firstListInclElmText) {
					valText = valText.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "\n";
				}
				incl += valText;
			}else if (rkind.getName().equals("exclusion")) {
				niveauList = "";
				niveauListHTML = 0;
				niveauListHTMLExclP = 0;
				String val = getHTMLExclLabelValue(rubric.getLabel().get(0)) + "\n";
				if(!firstListExclElm) {
					val = "<li>" + val.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "</li> \n";
				}
				exclHtml += val;
				String valText = getExclExclValue(rubric.getLabel().get(0)).replace("\n\t\t\t\t", "").replace("\n\t\t\t", "")+ "\n";
				if(!firstListExclElmText) {
					valText = valText.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "\n";
				}
				excl += valText;
			}
		}
		if (inclHtml.length() > 0) {
			String val = "<ul>" + inclHtml;
			if(niveauListHTMLInclA == 0) {
				val += "</ul>";
			}else {
				if(niveauListHTMLIncl3P && niveauListHTMLInclA == 3) {
					val += "</ul>";
				}
				if(niveauListHTMLIncl2P) {
					val += "</li> \n </ul> \n </li>";
				}
				if(niveauListHTMLIncl1P && !niveauListHTMLIncl2P){
					val += "</ul> \n </li>";
				}
				val += "</ul>";
			}
			
//			addClassHtmlInclusion(owlSubClass, val);
			addClassXInclusion(owlSubClass, incl.replace("\n\t\t\t\t\n\t\t\t\t\n\t\t\t", "").replace("\t\t\t\n\t\t\t\t\n", ""));
		}
		if (exclHtml.length() > 0) {
			String val = "<ul>" + exclHtml;
			if(niveauListHTMLExclA == 0) {
				val += "</ul>";
			}else {
				if(niveauListHTMLExcl3P && niveauListHTMLExclA == 3) {
					val += "</li> \n </ul>";
				}
				if(niveauListHTMLExcl2P) {
					val += "</li> \n </ul> \n </li>";
				}
				if(niveauListHTMLExcl1P && !niveauListHTMLExcl2P){
					val += "</ul> \n </li>";
				}
				val += "</ul>";
			}
//			addClassHtmlExclusion(owlSubClass, val);
			addClassExclusion(owlSubClass, excl.replace("\n\t\t\t\t\n\t\t\t\t\n\t\t\t", "").replace("\t\t\t\n\t\t\t\t\n", ""));
		}
		AddGeneratedBy(owlSubClass);
		addClassLabel(owlSubClass, supValue + " - \"" + subValue1 + "\"" + " - \"" + subValue2 + "\"");
		addClassKind(owlSubClass, "category");

	}
	
	private static void addSupClassExclusion(OWLClass owlClass, String supClass) {
		
		Class clazz = classMap.get(supClass);
		
		String excl = "";
		String exclHtml = "";
		
		listItemExcl = new ArrayList<>();
		listItemHTMLExcl = new ArrayList<>();
		
		niveauListHTMLExclA = 0;
		niveauListHTMLExcl1P = false;
		niveauListHTMLExcl2P = false;
		niveauListHTMLExcl3P = false;
		firstListExclElm = false;
		firstListExclElmText = false;
		for (Rubric rubric : clazz.getRubric()) {
			Object kind = rubric.getKind();
			RubricKind rkind = (RubricKind) kind;
			if (rkind.getName().equals("exclusion")) {
				niveauList = "";
				niveauListHTML = 0;
				niveauListHTMLExclP = 0;
				String val = getHTMLExclLabelValue(rubric.getLabel().get(0)) + "\n";
				if(!firstListExclElm) {
					val = "<li>" + val.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "</li> \n";
				}
				exclHtml += val;
				String valText = getExclExclValue(rubric.getLabel().get(0)).replace("\n\t\t\t\t", "").replace("\n\t\t\t", "")+ "\n";
				if(!firstListExclElmText) {
					valText = valText.replace("\n\t\t\t\t", " ").replace("\n\t\t\t", " ").replace("\n", " ").trim() + "\n";
				}
				excl += valText;
				
			}
		}
		
		if (exclHtml.length() > 0) {
			String val = "<ul>" + exclHtml;
			if(niveauListHTMLExclA == 0) {
				val += "</ul>";
			}else {
				if(niveauListHTMLExcl3P && niveauListHTMLExclA == 3) {
					val += "</li> \n </ul>";
				}
				if(niveauListHTMLExcl2P) {
					val += "</li> \n </ul> \n </li>";
				}
				if(niveauListHTMLExcl1P && !niveauListHTMLExcl2P){
					val += "</ul> \n </li>";
				}
				val += "</ul>";
			}
//			addClassHtmlExclusion(owlClass, val);
			addClassExclusion(owlClass, excl.replace("\n\t\t\t\t\n\t\t\t\t\n\t\t\t", "").replace("\t\t\t\n\t\t\t\t\n", ""));
		}
	
	}

	private static void addClassLabel(OWLClass owlClass, String value) {
		OWLAnnotation annot = fact.getOWLAnnotation(fact.getRDFSLabel(), fact.getOWLLiteral(value, "fr"));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassComment(OWLClass owlClass, String value) {
		OWLAnnotationProperty definition = new OWLAnnotationPropertyImpl(SKOSVocabulary.DEFINITION.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(definition, fact.getOWLLiteral(value, "fr"));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassKind(OWLClass owlClass, String value) {
		OWLAnnotationProperty classKind = new OWLAnnotationPropertyImpl(DCVocabulary.type.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(classKind, fact.getOWLLiteral(value));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassUsageDagger(OWLClass owlClass, String code) {
		if (classMap.containsKey(code)) {
		OWLAnnotationProperty classUsageDagger = new OWLAnnotationPropertyImpl(ATIHCIM10Vocabulary.hasCausality.getIRI());
		String Uri = "http://data.esante.gouv.fr/atih/cim10/" + code;
		OWLAnnotation annot = fact.getOWLAnnotation(classUsageDagger, IRI.create(Uri));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
		}
	}
	
	private static void addClassUsageDagger(OWLClass owlClass, Map<String,List<String>> mapCode) {
		for(String code : mapCode.keySet()) {
			if (classMap.containsKey(code)) {
				OWLAnnotationProperty classUsageDagger = new OWLAnnotationPropertyImpl(ATIHCIM10Vocabulary.hasCausality.getIRI());
				String Uri = "http://data.esante.gouv.fr/atih/cim10/" + code;
				OWLAnnotation annot = fact.getOWLAnnotation(classUsageDagger, IRI.create(Uri));
				
				List<OWLAnnotation> annots = new ArrayList<OWLAnnotation>();
				for(String label : mapCode.get(code)) {
					OWLAnnotationProperty wasDerivedFrom = new OWLAnnotationPropertyImpl(PROVVocabulary.WAS_DERIVED_FROM.getIRI());
					OWLAnnotation annot1 = fact.getOWLAnnotation(wasDerivedFrom, fact.getOWLLiteral(label , "fr"));
					annots.add(annot1);
				}
				
				OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot, annots);
				
				
				manager.applyChange(new AddAxiom(onto, axiom));
			}
		}
	}
	

	private static void addClassUsageAster(OWLClass owlClass, String code) {
		if (classMap.containsKey(code)) {
		OWLAnnotationProperty classUsageAster = new OWLAnnotationPropertyImpl(ATIHCIM10Vocabulary.hasManifestation.getIRI());
		String Uri = "http://data.esante.gouv.fr/atih/cim10/" + code;
		OWLAnnotation annot = fact.getOWLAnnotation(classUsageAster, IRI.create(Uri));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		
//		OWLAnnotationProperty wasDerivedFrom = new OWLAnnotationPropertyImpl(PROVVocabulary.WAS_DERIVED_FROM.getIRI());
//		OWLAnnotation annot1 = fact.getOWLAnnotation(wasDerivedFrom, fact.getOWLLiteral("causality test" , "fr"));
//		
//		OWLAxiom axiom2 = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot, new ArrayList() {{ add(annot1);	}});
//		
		manager.applyChange(new AddAxiom(onto, axiom));
		}
	}
	
	private static void addClassUsageAster(OWLClass owlClass, Map<String,List<String>> mapCode) {
		for(String code : mapCode.keySet()) {
			if (classMap.containsKey(code)) {
				OWLAnnotationProperty classUsageAster = new OWLAnnotationPropertyImpl(ATIHCIM10Vocabulary.hasManifestation.getIRI());
				String Uri = "http://data.esante.gouv.fr/atih/cim10/" + code;
				OWLAnnotation annot = fact.getOWLAnnotation(classUsageAster, IRI.create(Uri));
				List<OWLAnnotation> annots = new ArrayList<OWLAnnotation>();
				for(String label : mapCode.get(code)) {
					OWLAnnotationProperty wasDerivedFrom = new OWLAnnotationPropertyImpl(PROVVocabulary.WAS_DERIVED_FROM.getIRI());
					OWLAnnotation annot1 = fact.getOWLAnnotation(wasDerivedFrom, fact.getOWLLiteral(label , "fr"));
					annots.add(annot1);
				}
				OWLAxiom axiom2 = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot, annots);
				
				manager.applyChange(new AddAxiom(onto, axiom2));
			}
		}
	}

//	private static void addClassIntroduction(OWLClass owlClass, String value) {
//		OWLAnnotationProperty introduction = new OWLAnnotationPropertyImpl(SKOSVocabulary.NOTE.getIRI());
//		OWLAnnotation annot = fact.getOWLAnnotation(introduction, fact.getOWLLiteral(value));
//		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//		manager.applyChange(new AddAxiom(onto, axiom));
//	}

//	private static void addClassFootnote(OWLClass owlClass, String value) {
//		OWLAnnotationProperty footnote = fact.getOWLAnnotationProperty(ICDVocabulary.footnote.getIRI());
//		OWLAnnotation annot = fact.getOWLAnnotation(footnote, fact.getOWLLiteral(value));
//		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//		manager.applyChange(new AddAxiom(onto, axiom));
//	}

	private static void addClassNote(OWLClass owlClass, String value) {
		OWLAnnotationProperty classNote = new OWLAnnotationPropertyImpl(SKOSVocabulary.NOTE.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(classNote, fact.getOWLLiteral(value, "fr"));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}
	
	private static void addClassHtmlNote(OWLClass owlClass, String value) {
		OWLAnnotationProperty classNote = new OWLAnnotationPropertyImpl(SKOSVocabulary.NOTE.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(classNote, fact.getOWLLiteral(value, OWL2Datatype.RDF_XML_LITERAL));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassInclusion(OWLClass owlClass, String value) {
		OWLAnnotationProperty classInclusion = new OWLAnnotationPropertyImpl(SKOSVocabulary.ALTLABEL.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(classInclusion,
				fact.getOWLLiteral(value.replace(" :", "").replace("\n", "").replaceAll("\t+", " ").trim(), "fr"));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassXInclusion(OWLClass owlClass, String value) {
		OWLAnnotationProperty classInclusion = new OWLAnnotationPropertyImpl(XSkosVocabulary.inclusionNote.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(classInclusion,
				fact.getOWLLiteral(value, OWL2Datatype.RDF_LANG_STRING));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassExclusion(OWLClass owlClass, String value) {
		OWLAnnotationProperty classExclusion = new OWLAnnotationPropertyImpl(XSkosVocabulary.exclusionNote.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(classExclusion,
				fact.getOWLLiteral(value, OWL2Datatype.RDF_LANG_STRING));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}
	
	private static void addClassHtmlInclusion(OWLClass owlClass, String value) {
		OWLAnnotationProperty classInclusion = new OWLAnnotationPropertyImpl(XSkosVocabulary.inclusionNote.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(classInclusion,
				fact.getOWLLiteral(value, OWL2Datatype.RDF_XML_LITERAL));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

//	private static void addClassHtmlExclusion(OWLClass owlClass, String value) {
//		OWLAnnotationProperty classExclusion = new OWLAnnotationPropertyImpl(XSkosVocabulary.exclusionNote.getIRI());
//		OWLAnnotation annot = fact.getOWLAnnotation(classExclusion,
//				fact.getOWLLiteral(value, OWL2Datatype.RDF_XML_LITERAL));
//		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//		manager.applyChange(new AddAxiom(onto, axiom));
//	}

	private static void addClassDisjointExclusion(OWLClass owlClass, String value) throws IOException {
		
//		OWLAnnotationProperty classDisjointExclusion = new OWLAnnotationPropertyImpl(OWLRDFVocabulary.OWL_DISJOINT_WITH.getIRI());
		
//		OWLAnnotationProperty classDisjointExclusion = fact
//				.getOWLAnnotationProperty(OWLRDFVocabulary.OWL_DISJOINT_WITH.getIRI());
		OWLAnnotationProperty classATIHCIMExclusion = new OWLAnnotationPropertyImpl(ATIHCIM10Vocabulary.exclusion.getIRI());
//		OWLDataFactoryImpl OWLDataFactoryImpl = new OWLDataFactoryImpl();
		for (String code : value.split(":")) {
			for (String ref : code.split(",")) {
				if(ref.contains("quatrième")) {
					ref = ref.substring(0, ref.length()-30);
				}
				ref = ref.trim().replaceAll("-$", "").replaceAll(";$", "");
				if (classMap.containsKey(ref) || cimReferences.contains(ref)) {
					String Uri = "http://data.esante.gouv.fr/atih/cim10/" + ref.trim();
					
//					OWLAnnotation annot = fact.getOWLAnnotation(fact.getOWLDisjoint(), IRI.create(Uri));
//					OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//					manager.applyChange(new AddAxiom(onto, axiom));
					OWLAnnotation annot2 = fact.getOWLAnnotation(classATIHCIMExclusion, IRI.create(Uri));
					OWLAxiom axiom2 = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot2);
					manager.applyChange(new AddAxiom(onto, axiom2));
					
					OWLClass disjClass = fact.getOWLClass(IRI.create(Uri));
					OWLDisjointClassesAxiom disjointClassesAxiom = fact.getOWLDisjointClassesAxiom(disjClass, owlClass);
			        manager.addAxiom(onto, disjointClassesAxiom);
					
				} else if (!(PropertiesUtil.getPlagesReference(ref) == null)) {
					String refs = PropertiesUtil.getPlagesReference(ref);
					for(String rf : refs.split(";")) {
						String Uri = "http://data.esante.gouv.fr/atih/cim10/"+rf.trim();
//						OWLAnnotation annot = fact.getOWLAnnotation(fact.getOWLDisjoint(), IRI.create(Uri));
//						OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//						manager.applyChange(new AddAxiom(onto, axiom));
						OWLAnnotation annot2 = fact.getOWLAnnotation(classATIHCIMExclusion, IRI.create(Uri));
						OWLAxiom axiom2 = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot2);
						manager.applyChange(new AddAxiom(onto, axiom2));
						
						OWLClass disjClass = fact.getOWLClass(IRI.create(Uri));
						OWLDisjointClassesAxiom disjointClassesAxiom = fact.getOWLDisjointClassesAxiom(disjClass, owlClass);
				        manager.addAxiom(onto, disjointClassesAxiom);
					}
				} else if (ref.contains("–")) {
					for(String rf : ref.split("–")) {
						String Uri = "http://data.esante.gouv.fr/atih/cim10/"+rf.trim();
//						OWLAnnotation annot = fact.getOWLAnnotation(fact.getOWLDisjoint(), IRI.create(Uri));
//						OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//						manager.applyChange(new AddAxiom(onto, axiom));
						OWLAnnotation annot2 = fact.getOWLAnnotation(classATIHCIMExclusion, IRI.create(Uri));
						OWLAxiom axiom2 = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot2);
						manager.applyChange(new AddAxiom(onto, axiom2));
						OWLClass disjClass = fact.getOWLClass(IRI.create(Uri));
						OWLDisjointClassesAxiom disjointClassesAxiom = fact.getOWLDisjointClassesAxiom(disjClass, owlClass);
				        manager.addAxiom(onto, disjointClassesAxiom);
					}
				} else if (ref.contains("-")) {
					for(String rf : ref.split("-")) {
						String Uri = "http://data.esante.gouv.fr/atih/cim10/"+rf.trim();
//						OWLAnnotation annot = fact.getOWLAnnotation(fact.getOWLDisjoint(), IRI.create(Uri));
//						OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//						manager.applyChange(new AddAxiom(onto, axiom));
						OWLAnnotation annot2 = fact.getOWLAnnotation(classATIHCIMExclusion, IRI.create(Uri));
						OWLAxiom axiom2 = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot2);
						manager.applyChange(new AddAxiom(onto, axiom2));
						
						OWLClass disjClass = fact.getOWLClass(IRI.create(Uri));
						OWLDisjointClassesAxiom disjointClassesAxiom = fact.getOWLDisjointClassesAxiom(disjClass, owlClass);
				        manager.addAxiom(onto, disjointClassesAxiom);
					}
				} else {
					csvWriter.append(ref).append(";");
                    csvWriter.append("\n");
				}
			}
		}

	}

	private static void addClassCodingHint(OWLClass owlClass, String value) {
		OWLAnnotationProperty codingHint = new OWLAnnotationPropertyImpl(SKOSVocabulary.SCOPENOTE.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(codingHint, fact.getOWLLiteral(value, "fr"));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassCode(OWLClass owlClass, String code) {
		OWLAnnotationProperty classCode = new OWLAnnotationPropertyImpl(SkosVocabulary.notation.getIRI());
		OWLAnnotation annot = fact.getOWLAnnotation(classCode, fact.getOWLLiteral(code));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassParent(OWLClass owlClass, String sup) {
//		OWLAnnotationProperty broder = fact.getOWLAnnotationProperty(SKOSVocabulary.BROADER.getIRI());
		String broderUri = "http://data.esante.gouv.fr/atih/cim10/" + sup;
//		OWLAnnotation annot = fact.getOWLAnnotation(broder, IRI.create(broderUri));
//		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//		manager.applyChange(new AddAxiom(onto, axiom));

		OWLSubClassOfAxiom ax1 = fact.getOWLSubClassOfAxiom(owlClass, fact.getOWLClass(IRI.create(broderUri)));
		manager.applyChange(new AddAxiom(onto, ax1));
	}

//	private static void addClassChild(OWLClass owlClass, SubClass sub) {
//		OWLAnnotationProperty narrower = fact.getOWLAnnotationProperty(SKOSVocabulary.NARROWER.getIRI());
//		String narrowerUri = "http://data.esante.gouv.fr/atih/cim10/" + sub.getCode();
//		OWLAnnotation annot = fact.getOWLAnnotation(narrower, IRI.create(narrowerUri));
//		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
//		manager.applyChange(new AddAxiom(onto, axiom));
//	}

	private static void AddGeneratedBy(OWLClass owlClass) {
		OWLAnnotationProperty wasGeneratedBy = new OWLAnnotationPropertyImpl(PROVVocabulary.WAS_GENERATED_BY.getIRI());
		String uri = "http://data.esante.gouv.fr/atih/cim10/activity/ModifiedByConversion";
		OWLAnnotation annot = fact.getOWLAnnotation(wasGeneratedBy, IRI.create(uri));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

	private static void addClassMetaCreator(OWLClass owlClass, Meta meta) {
		OWLAnnotationProperty creator = new OWLAnnotationPropertyImpl(DCTVocabulary.creator.getIRI());
		String uri = "https://www.atih.sante.fr/";
		OWLAnnotation annot = fact.getOWLAnnotation(creator, IRI.create(uri));
		OWLAxiom axiom = fact.getOWLAnnotationAssertionAxiom(owlClass.getIRI(), annot);
		manager.applyChange(new AddAxiom(onto, axiom));
	}

//	private void addDesignationsForRubric(ConceptDefinitionComponent concept, Rubric rubric) {
//		if (rubric.getKind() instanceof RubricKind) {
//			RubricKind rkind = (RubricKind) rubric.getKind();
//			for (Label l : rubric.getLabel()) {
//				addDesignationForLabel(concept, rubric, rkind, l);
//			}
//		} else {
//			log.warn("Unexpected rubric kind " + rubric.getKind());
//		}
//	}

//	private void addDesignationForLabel(ConceptDefinitionComponent concept, Rubric rubric, RubricKind rkind, Label l) {
//		String v = getLabelValue(l);
//		if (v != null && v.length() > 0) {
//			ConceptDefinitionDesignationComponent desig = concept.addDesignation();
//			desig.setUse(new Coding().setCode(rkind.getName()));
//			desig.setValue(v);
//			desig.setLanguage(l.getLang());
//		} else {
//			log.warn("Skipping empty label for rubric " + rubric.getId());
//		}
//	}

	private static String getClassKindName(Object kind) {
		if (kind instanceof String) {
			return (String) kind;
		} else if (kind instanceof ClassKind) {
			return ((ClassKind) kind).getName();
		} else {
			log.warn("Unrecognized class kind:" + kind);
			return null;
		}
	}

	private static String getLabelValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				result += getLabelValue(cont);
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			return " [" + ((Reference) l).getContent() + "] ";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getLabelValue(cont);
			}
			return result;
		} else if (l instanceof Fragment) {
			String result = "";
			for (Object cont : ((Fragment) l).getContent()) {
				result += getLabelValue(cont);
			}
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "\t";
			} else if (term.getClazz().equals("subscript")) {
				return "_" + term.getContent();
			} else if (term.getClazz().equals("italics")) {
				return term.getContent();
			} else if (term.getClazz().equals("bold")) {
				return term.getContent();
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return term.getContent();
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += " - ";
				for (Object cont : item.getContent()) {
					result += getLabelValue(cont);
				}
				result += "\n";
			}
			return result;
		}else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}
	
	
	private static String getIntroductionValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				result += getIntroductionValue(cont);
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			return " [" + ((Reference) l).getContent() + "] ";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getIntroductionValue(cont);
			}
			return result;
		} else if (l instanceof Fragment) {
			String result = "";
			for (Object cont : ((Fragment) l).getContent()) {
				result += getIntroductionValue(cont);
			}
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "\t";
			} else if (term.getClazz().equals("subscript")) {
				return "_" + term.getContent();
			} else if (term.getClazz().equals("italics")) {
				return term.getContent();
			} else if (term.getClazz().equals("bold")) {
				return term.getContent();
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return term.getContent();
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += " - ";
				for (Object cont : item.getContent()) {
					result += getIntroductionValue(cont);
				}
				result += "\n";
			}
			return result;
		}else if (l instanceof Table) {
			String result = "";
			TBody tBody = ((Table) l).getTBody();
			Row row = tBody.getRow().get(0);
				if(row.getCell().size() == 2) {
					List<String> list1 = new ArrayList<String>();
					List<String> list2 = new ArrayList<String>();
					Cell cell1 = row.getCell().get(0);
					for (Object cont : cell1.getContent()) {
						if (cont instanceof fr.gouv.esante.smt.claml.models.List) {
							for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) cont).getListItem()) {
								for (Object cont1 : item.getContent()) {
									if(cont1 instanceof Para){
										list1.add(getIntroductionValue(cont1));
									}
								}
							}
						}else if(cont instanceof Para){
							list1.add(getIntroductionValue(cont));
						}
					}
					Cell cell2 = row.getCell().get(1);
					for (Object cont : cell2.getContent()) {
						if (cont instanceof fr.gouv.esante.smt.claml.models.List) {
							for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) cont).getListItem()) {
								for (Object cont1 : item.getContent()) {
									if(cont1 instanceof Para){
										list2.add(getIntroductionValue(cont1));
									}
								}
							}
						}else if(cont instanceof Para){
							list2.add(getIntroductionValue(cont));
						}
					}
					
					for(String val1 : list1) {
						for(String val2 : list2) {
							result += "<li>" + val1 + " " + val2 + "</li> \n";	
						}
					}
					
				}else if(row.getCell().size() == 3) {
					List<String> list1 = new ArrayList<String>();
					List<String> list2 = new ArrayList<String>();
					List<String> list3 = new ArrayList<String>();
					Cell cell1 = row.getCell().get(0);
					for (Object cont : cell1.getContent()) {
						if (cont instanceof fr.gouv.esante.smt.claml.models.List) {
							for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) cont).getListItem()) {
								for (Object cont1 : item.getContent()) {
									if(cont1 instanceof Para){
										list1.add(getIntroductionValue(cont1));
									}
								}
							}
						}else if(cont instanceof Para){
							list1.add(getIntroductionValue(cont));
						}
					}
					Cell cell2 = row.getCell().get(1);
					for (Object cont : cell2.getContent()) {
						if (cont instanceof fr.gouv.esante.smt.claml.models.List) {
							for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) cont).getListItem()) {
								for (Object cont1 : item.getContent()) {
									if(cont1 instanceof Para){
										list2.add(getIntroductionValue(cont1));
									}
								}
							}
						}else if(cont instanceof Para){
							list2.add(getIntroductionValue(cont));
						}
					}
					Cell cell3 = row.getCell().get(2);
					for (Object cont : cell3.getContent()) {
						if (cont instanceof fr.gouv.esante.smt.claml.models.List) {
							for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) cont).getListItem()) {
								for (Object cont1 : item.getContent()) {
									if(cont1 instanceof Para){
										list3.add(getIntroductionValue(cont1));
									}
								}
							}
						}else if(cont instanceof Para){
							list3.add(getIntroductionValue(cont));
						}
					}
					
					for(String val1 : list1) {
						for(String val2 : list2) {
							for(String val3 : list3) {
								result += "<li>" + val1 + " " + val2 + " " + val3 + "</li>";	
							}
						}
					}
				}
			
			return result;
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}
	
	private static String getInclExclValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				if (cont instanceof String && (((String) cont).equals("\n\t\t\t\t") && ((String) cont).equals("\n\t\t\t"))) {
					
				}else {
					result += getInclExclValue(cont);
				}
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			return " [" + ((Reference) l).getContent() + "] ";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getInclExclValue(cont);
			}
			return result;
		} else if (l instanceof Fragment) {
			String result = "";
			String value = "";
			for (Object cont : ((Fragment) l).getContent()) {
				value += getInclExclValue(cont);
			}
			if(value.contains(":")) {
				value += "\n";
			}
				if(((Fragment) l).getType().equals("list")) {
					firstListInclElmText = true;
					if(!listItemIncl.contains(value)) {
						listItemIncl.add(value);
						if(listItemIncl.size() == 1) {
							result += value;
						}else if(value.contains("•")){
							result += niveauList + value;	
						}else {
							result += niveauList + "- " + value;
						}
					}else {
						//result += " ";
					}
					niveauList += " ";
				}else if(((Fragment) l).getType().equals("item")) {
					result += " " + value + " ";
				} else {
					result += "\t" + value;
				}
			
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "\t";
			} else if (term.getClazz().equals("subscript")) {
				return "_" + term.getContent();
			} else if (term.getClazz().equals("italics")) {
				return term.getContent();
			} else if (term.getClazz().equals("bold")) {
				return term.getContent();
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return term.getContent();
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += " - ";
				for (Object cont : item.getContent()) {
					result += getInclExclValue(cont);
				}
				result += "";
			}
			return result.replaceAll("\n", "_");
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}
	
	
	private static String getExclExclValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				if (cont instanceof String && (((String) cont).equals("\n\t\t\t\t") && ((String) cont).equals("\n\t\t\t"))) {
					
				}else {
					result += getExclExclValue(cont);
				}
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			return " [" + ((Reference) l).getContent() + "] ";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getExclExclValue(cont);
			}
			return result;
		} else if (l instanceof Fragment) {
			String result = "";
			String value = "";
			for (Object cont : ((Fragment) l).getContent()) {
				value += getExclExclValue(cont);
			}
			if(value.contains(":")) {
				value += "\n";
			}
				if(((Fragment) l).getType().equals("list")) {
					firstListExclElmText = true;
					if(!listItemExcl.contains(value)) {
						listItemExcl.add(value);
						if(listItemExcl.size() == 1) {
							result += value;
						}else if(value.contains("•")){
							result += niveauList + value;	
						}else {
							result += niveauList + "- " + value;
						}
					}else {
						//result += " ";
					}
					niveauList += " ";
				} else if(((Fragment) l).getType().equals("item")) {
					result += value + " ";
				} else {
					result += "\t" + value;
				}
			
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "\t";
			} else if (term.getClazz().equals("subscript")) {
				return "_" + term.getContent();
			} else if (term.getClazz().equals("italics")) {
				return term.getContent();
			} else if (term.getClazz().equals("bold")) {
				return term.getContent();
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return term.getContent();
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += " - ";
				for (Object cont : item.getContent()) {
					result += getExclExclValue(cont);
				}
				result += "";
			}
			return result.replaceAll("\n", "_");
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}
	
	
	
	private static String getLabelValueWithoutReference(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				result += getLabelValueWithoutReference(cont);
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			return "";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getLabelValueWithoutReference(cont);
			}
			return result;
		} else if (l instanceof Fragment) {
			String result = "";
			for (Object cont : ((Fragment) l).getContent()) {
				result += getLabelValueWithoutReference(cont);
			}
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "\t";
			} else if (term.getClazz().equals("subscript")) {
				return "_" + term.getContent();
			} else if (term.getClazz().equals("italics")) {
				return term.getContent();
			} else if (term.getClazz().equals("bold")) {
				return term.getContent();
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return term.getContent();
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += " - ";
				for (Object cont : item.getContent()) {
					result += getLabelValueWithoutReference(cont);
				}
				result += "\n";
			}
			return result;
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}

	private static String getDefValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				result += getDefValue(cont);
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				if (((Para) l).getClazz().equals("chpt-spec1-last") || ((Para) l).getClazz().equals("chpt-spec2-last"))
					result += getDefValue(cont);
			}
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "#";
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return term.getContent();
			}
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}

	private static String getAltLabelValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				result += getAltLabelValue(cont);
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			return "";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getAltLabelValue(cont);
			}
			return result;
		} else if (l instanceof Fragment) {
			String result = "";
			for (Object cont : ((Fragment) l).getContent()) {
				result += getAltLabelValue(cont);
			}
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "\t";
			} else if (term.getClazz().equals("subscript")) {
				return "_" + term.getContent();
			} else if (term.getClazz().equals("italics")) {
				return term.getContent();
			} else if (term.getClazz().equals("bold")) {
				return term.getContent();
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return term.getContent();
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += " - ";
				for (Object cont : item.getContent()) {
					result += getAltLabelValue(cont);
				}
				result += "\n";
			}
			return result;
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}

	
	
	private static String getHTMLInclLabelValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				if (cont instanceof String && !((String) cont).equals("\n\t\t\t\t") && !((String) cont).equals("\n\t\t\t")) { // This is a hack, check all contents?
					if(niveauListHTMLInclA == 1) {
						result += "</ul> \n </li> \n <li>" + (String) cont + "</li>";
						niveauListHTMLInclA = 0;
						listItemHTMLIncl.clear();
						niveauListHTMLIncl1P = false;
					}else if(niveauListHTMLInclA == 2) {
						result += "</li> \n </ul> \n </li> \n <li>" + (String) cont + "</li>";
						niveauListHTMLInclA = 0;
						listItemHTMLIncl.clear();
						niveauListHTMLIncl1P = false;
					}else if(niveauListHTMLInclA == 3) {
						result += "</ul> \n </li> \n </ul> \n </li> \n  \n <li>" + (String) cont + "</li>";
						niveauListHTMLInclA = 0;
						listItemHTMLIncl.clear();
						niveauListHTMLIncl1P = false;
					}else if(!firdtListInclElm) {
						result += (String) cont;
					}else {
						result += "<li>" + (String) cont + "</li>";
					}
//					return (String) cont;
				}else {
					result += getHTMLInclLabelValue(cont);
				}
			}
			return result + "";
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			String ref = "";
			if (((Reference) l).getContent().replace(".-", "").replace(".–", "").length() < 6) {
				if (null != ((Reference) l).getUsage()) {
					Object usage = ((Reference) l).getUsage();
					UsageKind uk = (UsageKind) usage;
					String us = uk.getName();
					ref = "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/"
							+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "\" data-usage=\""+ us + "\">"
							+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "</span>";
				}else {
					ref = "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/"
						+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "\">"
						+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "</span>";
				}
			} else {
				String value = ((Reference) l).getContent().replace(".-", "").replace(".–", "");
				if(value.contains("quatrième")) {
					value = value.substring(0, value.length()-30);
				}
				for (String code : value.split(":")) {
					for (String rf : code.split(",")) {
						if (!rf.contains("-")) {
							ref += "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/" + rf.trim() + "\">"
									+ rf.trim() + "</span> ";
						} else {
							for (String cd : rf.split("-")) {
								ref += "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/" + cd.trim() + "\">"
										+ cd.trim() + "</span> - ";
							}
							ref = ref.substring(0, ref.length() - 2);
						}
					}
				}
			}
			return " [ " + ref + " ]";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getHTMLInclLabelValue(cont);
			}
			return result + "";
		} else if (l instanceof Fragment) {
			String result = "";
			String value = "";
			for (Object cont : ((Fragment) l).getContent()) {
				value += getHTMLInclLabelValue(cont);
				
			}
				
				if(((Fragment) l).getType().equals("list")) {
					firdtListInclElm = true;
					if(listItemHTMLIncl.isEmpty()) {
						niveauListHTMLInclA = 1;
					}
					niveauListHTMLInclP++;
					if(!listItemHTMLIncl.contains(value)) {
						listItemHTMLIncl.add(value);						
						
						
						if(niveauListHTMLInclP == 1 && !niveauListHTMLIncl1P) {
							result +=" <li>" + value + " \n <ul>";
							niveauListHTMLIncl1P = true;
							niveauListHTMLIncl2P = false;
						}else if(niveauListHTMLInclP == 1 && niveauListHTMLIncl1P && niveauListHTMLInclA == 1) {
							result += "</ul> \n </li> \n <li>" + value + " \n <ul>";
							niveauListHTMLIncl2P = false;
						}else if(niveauListHTMLInclP == 1 && niveauListHTMLIncl1P && niveauListHTMLInclA > 1) {
							result += "</li> \n </ul> \n </li> \n <li>" + value + " \n <ul>";
							niveauListHTMLIncl2P = false;
						}
						
						if(niveauListHTMLInclP == 2 && !niveauListHTMLIncl2P) {
							result += "\n <li>" + value;
							niveauListHTMLIncl2P = true;
							niveauListHTMLIncl3P = false;
						}else if(niveauListHTMLInclP == 2 && niveauListHTMLInclA == niveauListHTMLInclP) {
							result += "</li> \n <li>" + value ;
							niveauListHTMLIncl3P = false;
						}else if(niveauListHTMLInclP == 2 && listItemHTMLIncl.size() > 2 && niveauListHTMLInclA > niveauListHTMLInclP) {
							result += "\n </ul> \n </li> \n <li>" + value ;
							niveauListHTMLIncl3P = false;
							niveauListHTMLInclA = niveauListHTMLInclP;
						}
						
						if(niveauListHTMLInclP == 3 && !niveauListHTMLIncl3P) {
							result += "<ul> \n <li>" + value + "</li>";
							niveauListHTMLIncl3P = true;
						}else if(niveauListHTMLInclP == 3 ){
							result += "<li>" + value + "</li>";
						}
						if(niveauListHTMLInclA < niveauListHTMLInclP) {
							niveauListHTMLInclA = niveauListHTMLInclP;
						}
						
						
					}
					
					
				} else if(((Fragment) l).getType().equals("item") && !firdtListInclElm){
					result +=  value;
				} else {
					result +=  "<li>" + value + "</li>";
				}
				
				
			
			
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			return term.getContent();
			
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += "";
				for (Object cont : item.getContent()) {
					result += getHTMLInclLabelValue(cont);
				}
				result += "\n";
			}
			return result + "";
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}
	
	
	private static String getHTMLExclLabelValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				if (cont instanceof String && !((String) cont).equals("\n\t\t\t\t") && !((String) cont).equals("\n\t\t\t")) { // This is a hack, check all contents?
					if(niveauListHTMLExclA == 1) {
						result += "</ul> \n </li> \n <li>" + (String) cont + "</li>";
						niveauListHTMLExclA = 0;
						listItemHTMLExcl.clear();
						niveauListHTMLExcl1P = false;
					}else if(niveauListHTMLExclA == 2) {
						result += "</li> \n </ul> \n </li> \n <li>" + (String) cont + "</li>";
						niveauListHTMLExclA = 0;
						listItemHTMLExcl.clear();
						niveauListHTMLExcl1P = false;
					}else if(niveauListHTMLExclA == 3) {
						result += "</li> \n </ul> \n </li> \n </ul> \n </li> \n  \n <li>" + (String) cont + "</li>";
						niveauListHTMLExclA = 0;
						listItemHTMLExcl.clear();
						niveauListHTMLExcl1P = false;
					}else if(!firstListExclElm) {
						result += (String) cont;
					}else {
						result += "<li>" + (String) cont + "</li>";
					}
//					return (String) cont;
				}else {
					result += getHTMLExclLabelValue(cont);
				}
			}
			return result + "";
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			String ref = "";
			if (((Reference) l).getContent().replace(".-", "").replace(".–", "").length() < 6) {
				if (null != ((Reference) l).getUsage()) {
					Object usage = ((Reference) l).getUsage();
					UsageKind uk = (UsageKind) usage;
					String us = uk.getName();
					ref = "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/"
							+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "\" data-usage=\""+ us + "\">"
							+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "</span>";
				}else {
					ref = "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/"
						+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "\">"
						+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "</span>";
				}
			} else {
				String value = ((Reference) l).getContent().replace(".-", "").replace(".–", "");
				if(value.contains("quatrième")) {
					value = value.substring(0, value.length()-30);
				}
				for (String code : value.split(":")) {
					for (String rf : code.split(",")) {
						if (!rf.contains("-")) {
							ref += "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/" + rf.trim() + "\">"
									+ rf.trim() + "</span> ";
						} else {
							for (String cd : rf.split("-")) {
								ref += "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/" + cd.trim() + "\">"
										+ cd.trim() + "</span> - ";
							}
							ref = ref.substring(0, ref.length() - 2);
						}
					}
				}
			}
			return " [ " + ref + " ]";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getHTMLExclLabelValue(cont);
			}
			return result + "";
		} else if (l instanceof Fragment) {
			String result = "";
			String value = "";
			for (Object cont : ((Fragment) l).getContent()) {
				value += getHTMLExclLabelValue(cont);
				
			}
				
				if(((Fragment) l).getType().equals("list")) {
					firstListExclElm = true;
					if(listItemHTMLExcl.isEmpty()) {
						niveauListHTMLExclA = 1;
					}
					niveauListHTMLExclP++;
					if(!listItemHTMLExcl.contains(value)) {
						if(niveauListHTMLExclP == 1) {
							listItemHTMLExcl.clear();
						}
						listItemHTMLExcl.add(value);						
						
						
						if(niveauListHTMLExclP == 1 && !niveauListHTMLExcl1P) {
							result +=" <li>" + value + " \n <ul>";
							niveauListHTMLExcl1P = true;
							niveauListHTMLExcl2P = false;
						}else if(niveauListHTMLExclP == 1 && niveauListHTMLExcl1P && niveauListHTMLExclA == 1) {
							result += "</ul> \n </li> \n <li>" + value + " \n <ul>";
							niveauListHTMLExcl2P = false;
						}else if(niveauListHTMLExclP == 1 && niveauListHTMLExcl1P && niveauListHTMLExclA == 2) {
							result += "</li> \n </ul> \n </li> \n <li>" + value + " \n <ul>";
							niveauListHTMLExcl2P = false;
						}else if(niveauListHTMLExclP == 1 && niveauListHTMLExcl1P && niveauListHTMLExclA == 3) {
							result += "</li> \n </ul> \n </li> \n </ul> \n </li> \n <li>" + value + " \n <ul>";
							niveauListHTMLExcl2P = false;
						}
						
						if(niveauListHTMLExclP == 2 && !niveauListHTMLExcl2P) {
							result += "\n <li>" + value;
							niveauListHTMLExcl2P = true;
							niveauListHTMLExcl3P = false;
							niveauListHTMLExclA = 2;
						}else if(niveauListHTMLExclP == 2 && niveauListHTMLExclA == 3) {
							result += "</li> \n </ul> \n </li> \n <li>" + value ;
							niveauListHTMLExclA = 2;
							niveauListHTMLExcl3P = false;
						}else if(niveauListHTMLExclP == 2 && niveauListHTMLExclA == 4) {
							result += "</ul> \n </li> \n </ul> \n </li> \n <li>" + value ;
							niveauListHTMLExclA = 2;
							niveauListHTMLExcl4P = false;
						}else if(niveauListHTMLExclP == 2 && niveauListHTMLExclA == niveauListHTMLExclP) {
							result += "</li> \n <li>" + value ;
							niveauListHTMLExcl3P = false;
							niveauListHTMLExclA = 2;
						}else if(niveauListHTMLExclP == 2 && listItemHTMLExcl.size() > 2 && niveauListHTMLExclA > niveauListHTMLExclP) {
							result += "</li> \n <li>" + value ;
							niveauListHTMLExcl3P = false;
							niveauListHTMLExclA = niveauListHTMLExclP;
						}
						
						if(niveauListHTMLExclP == 3 && !niveauListHTMLExcl3P) {
							result += "<ul> \n <li>" + value;
							niveauListHTMLExcl3P = true;
							niveauListHTMLExcl4P = false;
							niveauListHTMLExclA = 3;
						}else if(niveauListHTMLExclP == 3 && niveauListHTMLExclA == 4){
							result += "</ul> \n </li> \n <li>" + value;
							niveauListHTMLExclA = 3;
						}else if(niveauListHTMLExclP == 3 ){
							result += "</li> \n <li>" + value;
							niveauListHTMLExclA = 3;
						}
						
						if(niveauListHTMLExclP == 4 && !niveauListHTMLExcl4P) {
							result += "<ul> \n <li>" + value + "</li>";
							niveauListHTMLExcl4P = true;
						}else if(niveauListHTMLExclP == 4 ){
							result += "<li>" + value + "</li>";
						}
						
						
						if(niveauListHTMLExclA < niveauListHTMLExclP) {
							niveauListHTMLExclA = niveauListHTMLExclP;
						}
						
			
					}else {

					}
					
					
				} else if(((Fragment) l).getType().equals("item") && !firstListExclElm){
					result +=  value;
				} else {
					result +=  "<li>" + value + "</li>";
				}
				
				
			
			
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			return term.getContent();
			
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += "";
				for (Object cont : item.getContent()) {
					result += getHTMLExclLabelValue(cont);
				}
				result += "\n";
			}
			return result + "";
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}
	
	
	
	
	
	private static String getHTMLLabelValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				result += getHTMLLabelValue(cont);
			}
			return result + "";
		} else if (l instanceof String) { // This is a hack, check all contents?
			return (String) l;
		} else if (l instanceof Reference) {
			String ref = "";
			if (((Reference) l).getContent().replace(".-", "").replace(".–", "").length() < 6) {
				if (null != ((Reference) l).getUsage()) {
					Object usage = ((Reference) l).getUsage();
					UsageKind uk = (UsageKind) usage;
					String us = uk.getName();
					ref = "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/"
							+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "\" data-usage=\""+ us + "\">"
							+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "</span>";
				}else {
					ref = "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/"
						+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "\">"
						+ ((Reference) l).getContent().replace(".-", "").replace(".–", "") + "</span>";
				}
			} else {
				String value = ((Reference) l).getContent().replace(".-", "").replace(".–", "");
				if(value.contains("quatrième")) {
					value = value.substring(0, value.length()-30);
				}
				for (String code : value.split(":")) {
					for (String rf : code.split(",")) {
						if (!rf.contains("-")) {
							ref += "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/" + rf.trim() + "\">"
									+ rf.trim() + "</span> ";
						} else {
							for (String cd : rf.split("-")) {
								ref += "<span data-uri=\"http://data.esante.gouv.fr/atih/cim10/" + cd.trim() + "\">"
										+ cd.trim() + "</span> - ";
							}
							ref = ref.substring(0, ref.length() - 2);
						}
					}
				}
			}
			return " [ " + ref + " ]";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getHTMLLabelValue(cont);
			}
			return result + "";
		} else if (l instanceof Fragment) {
			String result = "";
			for (Object cont : ((Fragment) l).getContent()) {
//				result += getHTMLLabelValue(cont);
				
				String value = getHTMLLabelValue(cont);
				if(((Fragment) l).getType().equals("list")) {
					
					if(!listItemHTMLExcl.contains(value)) {
						listItemHTMLExcl.add(value);
						if(niveauListHTML < 10) {
							result += value;
						}
						if(listItemHTMLExcl.size() == 1) {
							result += value;
						}else if(value.contains("•")){
							result += niveauListHTML + value;	
						}else {
							result += niveauListHTML + "" + value;
						}
					}else {
						//result += " ";
					}
				} else {
					result +=  "<li>" + value + "</li>";
				}
				
				
			}
			
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "";
			} else if (term.getClazz().equals("subscript")) {
				return "_" + term.getContent();
			} else if (term.getClazz().equals("italics")) {
				return term.getContent();
			} else if (term.getClazz().equals("bold")) {
				return term.getContent();
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return term.getContent();
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "<li>";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += " - ";
				for (Object cont : item.getContent()) {
					result += getHTMLLabelValue(cont);
				}
				result += "\n";
			}
			return result + "</li>";
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}

	private static String getReferenceValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				result += getReferenceValue(cont);
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return "";
		} else if (l instanceof Reference) {
			return ((Reference) l).getContent() + ":";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getReferenceValue(cont);
			}
			return result;
		} else if (l instanceof Fragment) {
			String result = "";
			for (Object cont : ((Fragment) l).getContent()) {
				result += getReferenceValue(cont);
			}
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "";
			} else if (term.getClazz().equals("subscript")) {
				return "";
			} else if (term.getClazz().equals("italics")) {
				return "";
			} else if (term.getClazz().equals("bold")) {
				return "";
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return "";
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += "";
				for (Object cont : item.getContent()) {
					result += getReferenceValue(cont);
				}
				result += "";
			}
			return result;
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}

	private static String getReferenceUsageValue(Object l) {
		if (l instanceof Label) {
			String result = "";
			for (Object cont : ((Label) l).getContent()) {
				result += getReferenceUsageValue(cont);
			}
			return result;
		} else if (l instanceof String) { // This is a hack, check all contents?
			return "";
		} else if (l instanceof Reference) {
			String us = "";
			if (null != ((Reference) l).getUsage()) {
				Object usage = ((Reference) l).getUsage();
				UsageKind uk = (UsageKind) usage;
				us = uk.getName();
			}
			return ((Reference) l).getContent() + ":" + us + ",";
		} else if (l instanceof Para) {
			String result = "";
			for (Object cont : ((Para) l).getContent()) {
				result += getReferenceUsageValue(cont);
			}
			return result;
		} else if (l instanceof Fragment) {
			String result = "";
			for (Object cont : ((Fragment) l).getContent()) {
				result += getReferenceUsageValue(cont);
			}
			return result;
		} else if (l instanceof Term) {
			Term term = (Term) l;
			if (term.getClazz().equals("tab")) {
				return "";
			} else if (term.getClazz().equals("subscript")) {
				return "";
			} else if (term.getClazz().equals("italics")) {
				return "";
			} else if (term.getClazz().equals("bold")) {
				return "";
			} else {
				log.warn("Unrecognized Term class:" + term.getClazz());
				return "";
			}
		} else if (l instanceof fr.gouv.esante.smt.claml.models.List) {
			String result = "";
			for (ListItem item : ((fr.gouv.esante.smt.claml.models.List) l).getListItem()) {
				result += "";
				for (Object cont : item.getContent()) {
					result += getReferenceUsageValue(cont);
				}
				result += "";
			}
			return result;
		} else {
			log.warn("Ignoring non-String label contents on Label (" + l.getClass().getSimpleName() + ")");
			return l.getClass().getSimpleName().toUpperCase();
		}
	}

}